-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Stuff.Stuff

/-!
# Bridge/Stuff/Unstuff: the extracted `unstuff` refines the model's `decode`

`[EXTRACTED: aeneas + bridge]` -- the decode side of the byte-stuffing bridge. `unstuff_refines`
proves that the Charon/Aeneas extraction of `rust/src/stuff.rs`'s `unstuff` agrees with
`FramedChannel.Stuff.decode` on every input slice: on success the same payload and the same residual
bytes, and on failure the model fails too.

## The variable-stride loop

Unlike `varint`'s fixed five-iteration loops, this loop advances by **one or two** indices depending
on whether the byte it reads is an escape, so the decreasing measure is `wire.len() - i` rather than
a counter. Its body has seven exits: the terminating flag (`Ok`), an escape followed by either
escaped value (two `cont` steps of stride two), an escape followed by anything else (`Err BadEscape`),
an escape at the very end and a wire that runs out (both `Err Truncated`), and an ordinary byte
(`cont`, stride one).

## The invariant

`UnstuffInv` says the model's own computation is unchanged by what the loop has done so far: running
the model's `unstuff` from the accumulated output, on the wire's remaining suffix, gives exactly what
running it from empty on the whole wire gives. The model accumulates in reverse and the extracted
code accumulates in order, so the accumulator is related by `(bytesOf out).reverse`.

Stating the invariant as that equation, rather than as a case analysis, is what makes the seven exits
cheap: each one is discharged by a single model-side equation lemma (the `unstuff_*` group below),
proved here rather than in the core model so that the approved `Model/Stuff/Theorems.lean` did not
have to change.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuff
open framed_channel

/-! ## Model-side equation lemmas

Each is one branch of the model's `unstuff`, stated so that it applies whether or not the wire has a
further byte after the one being read. `Model/Stuff/Theorems.lean`'s `unstuff_cons_plain` carries a
`w ≠ []` side condition; `unstuff_plain` below drops it, because the empty case is also an agreement
(both sides refuse), and that is what lets the loop's plain branch and its final `Truncated` exit
share one lemma. -/

theorem unstuff_nil (acc : List Nat) : FramedChannel.Stuff.unstuff acc [] = .fail := rfl

/-- The terminating flag ends the frame, whatever follows it. -/
theorem unstuff_marker (acc rest : List Nat) :
    FramedChannel.Stuff.unstuff acc (FramedChannel.Stuff.marker :: rest)
      = .ok (acc.reverse, rest) := by
  cases rest with
  | nil => rw [FramedChannel.Stuff.unstuff.eq_2]; simp
  | cons x xs => rw [FramedChannel.Stuff.unstuff.eq_3]; simp

/-- An ordinary byte is payload, whatever follows it (including nothing: both sides refuse). -/
theorem unstuff_plain (b : Nat) (h1 : b ≠ FramedChannel.Stuff.marker)
    (h2 : b ≠ FramedChannel.Stuff.esc) (acc rest : List Nat) :
    FramedChannel.Stuff.unstuff acc (b :: rest)
      = FramedChannel.Stuff.unstuff (b :: acc) rest := by
  cases rest with
  | nil => rw [FramedChannel.Stuff.unstuff.eq_2, unstuff_nil]; simp only [if_neg h1]
  | cons x xs => rw [FramedChannel.Stuff.unstuff.eq_3]; simp only [if_neg h1, if_neg h2]

/-- An escape at the very end of the wire refuses. -/
theorem unstuff_esc_last (acc : List Nat) :
    FramedChannel.Stuff.unstuff acc [FramedChannel.Stuff.esc] = .fail := by
  rw [FramedChannel.Stuff.unstuff.eq_2]
  simp only [if_neg FramedChannel.Stuff.esc_ne_marker]

/-- An escaped flag byte unescapes to the flag. -/
theorem unstuff_esc_marker (acc rest : List Nat) :
    FramedChannel.Stuff.unstuff acc
        (FramedChannel.Stuff.esc :: FramedChannel.Stuff.escMarker :: rest)
      = FramedChannel.Stuff.unstuff (FramedChannel.Stuff.marker :: acc) rest := by
  rw [FramedChannel.Stuff.unstuff.eq_3]
  simp [FramedChannel.Stuff.esc_ne_marker]

/-- An escaped escape byte unescapes to the escape byte. -/
theorem unstuff_esc_esc (acc rest : List Nat) :
    FramedChannel.Stuff.unstuff acc (FramedChannel.Stuff.esc :: FramedChannel.Stuff.escEsc :: rest)
      = FramedChannel.Stuff.unstuff (FramedChannel.Stuff.esc :: acc) rest := by
  rw [FramedChannel.Stuff.unstuff.eq_3]
  simp [FramedChannel.Stuff.esc_ne_marker,
    show FramedChannel.Stuff.escEsc ≠ FramedChannel.Stuff.escMarker from by decide]

/-- An escape followed by neither escaped value refuses. -/
theorem unstuff_esc_bad (c : Nat) (h1 : c ≠ FramedChannel.Stuff.escMarker)
    (h2 : c ≠ FramedChannel.Stuff.escEsc) (acc rest : List Nat) :
    FramedChannel.Stuff.unstuff acc (FramedChannel.Stuff.esc :: c :: rest) = .fail := by
  rw [FramedChannel.Stuff.unstuff.eq_3]
  simp [FramedChannel.Stuff.esc_ne_marker, h1, h2]

/-! ## Reading a slice index

Two small list facts, used at every branch of the loop to turn the extracted `Slice.get`'s
`Option` postcondition into an index bound plus the element itself. -/

theorem getElem?_some_lt {α : Type} {l : List α} {k : Nat} {a : α} (h : l[k]? = some a) :
    k < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none_iff.mpr (by omega)] at h
  simp at h

theorem eq_getElem_of_getElem? {α : Type} {l : List α} {k : Nat} {a : α} (h : l[k]? = some a)
    (hk : k < l.length) : a = l[k] := by
  rw [List.getElem?_eq_getElem hk] at h
  exact (Option.some.inj h).symm

/-! ## The loop invariant and the loop's postcondition -/

/-- What the extracted `unstuff` must establish about its own return value: on success the model
decodes the wire to the same payload and the same residual, and on failure the model refuses too. -/
def UnstuffPost (wire : Slice Std.U8)
    (r : core.result.Result ((alloc.vec.Vec Std.U8) × Std.Usize) stuff.UnstuffError) : Prop :=
  match r with
  | .Ok (out, k) => k.val ≤ wire.val.length ∧
      FramedChannel.Stuff.decode (bytesOf wire.val)
        = .ok (bytesOf out.val, (bytesOf wire.val).drop k.val)
  | .Err _ => FramedChannel.Stuff.decode (bytesOf wire.val) = .fail

/-- The loop invariant: what the model computes from here is what the model computes from the
start. -/
def UnstuffInv (wire : Slice Std.U8) (x : alloc.vec.Vec Std.U8 × Std.Usize) : Prop :=
  x.2.val ≤ wire.val.length ∧ x.1.val.length ≤ x.2.val ∧
    FramedChannel.Stuff.unstuff (bytesOf x.1.val).reverse ((bytesOf wire.val).drop x.2.val)
      = FramedChannel.Stuff.unstuff [] (bytesOf wire.val)

/-- Pushing one byte prepends its value to the model's reversed accumulator. -/
theorem bytesOf_push_reverse (out : alloc.vec.Vec Std.U8) (x : Std.U8) :
    (bytesOf (out.val ++ [x])).reverse = x.val :: (bytesOf out.val).reverse := by
  rw [bytesOf_append]; simp [bytesOf]

/-- The loop lemma. -/
theorem unstuff_loop_refines (wire : Slice Std.U8) (x : alloc.vec.Vec Std.U8 × Std.Usize)
    (hx : UnstuffInv wire x) :
    stuff.unstuff_loop wire x.1 x.2 ⦃ r => UnstuffPost wire r ⦄ := by
  unfold stuff.unstuff_loop
  apply loop.spec_decr_nat
    (measure := fun (x : alloc.vec.Vec Std.U8 × Std.Usize) => wire.val.length - x.2.val)
    (inv := UnstuffInv wire)
  · rintro ⟨out, i⟩ ⟨hile, hout, heq⟩
    simp only at hile hout heq
    -- the two exits that happen once the index has reached the end of the wire
    have hend : wire.val.length ≤ i.val → FramedChannel.Stuff.decode (bytesOf wire.val) = .fail := by
      intro hge
      rw [FramedChannel.Stuff.decode, ← heq,
        List.drop_eq_nil_of_le (by rw [bytesOf_length]; omega), unstuff_nil]
    unfold stuff.unstuff_loop.body
    step*
    · -- `get` at `i` returned `none`: the wire has run out
      simp only [UnstuffPost]
      refine hend ?_
      have hnone : o = none := ‹o = none›
      rw [hnone] at o_post
      exact List.getElem?_eq_none_iff.mp o_post.symm
    · -- the terminating flag: the frame ends here and the rest of the wire is the residual
      have hsome : o = some b := ‹o = some b›
      have hbm : b = stuff.MARKER := ‹b = stuff.MARKER›
      have hget : wire.val[i.val]? = some b := by rw [← o_post, hsome]
      have hklt : i.val < wire.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none_iff.mpr (show wire.val.length ≤ i.val by omega)] at hget
        simp at hget
      have hb : b = wire.val[i.val] := by
        rw [List.getElem?_eq_getElem hklt] at hget
        exact (Option.some.inj hget).symm
      have hd1 : (bytesOf wire.val).drop i.val
          = b.val :: (bytesOf wire.val).drop (i.val + 1) := by
        rw [bytesOf_drop_cons wire.val i.val hklt, hb]
      have hbv : b.val = FramedChannel.Stuff.marker := by rw [hbm, marker_eq]
      simp only [UnstuffPost]
      refine ⟨by rw [i2_post]; omega, ?_⟩
      rw [FramedChannel.Stuff.decode, ← heq, hd1, hbv, unstuff_marker,
        List.reverse_reverse, i2_post]
    · -- an escape at the very end of the wire
      have hsome : o = some b := ‹o = some b›
      have hbe : b = stuff.ESC := ‹b = stuff.ESC›
      have hnone1 : o1 = none := ‹o1 = none›
      have hget : wire.val[i.val]? = some b := by rw [← o_post, hsome]
      have hklt : i.val < wire.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none_iff.mpr (show wire.val.length ≤ i.val by omega)] at hget
        simp at hget
      have hge2 : wire.val.length ≤ i.val + 1 := by
        rw [hnone1, i2_post] at o1_post
        exact List.getElem?_eq_none_iff.mp o1_post.symm
      have hb : b = wire.val[i.val] := by
        rw [List.getElem?_eq_getElem hklt] at hget
        exact (Option.some.inj hget).symm
      have hbv : b.val = FramedChannel.Stuff.esc := by rw [hbe, esc_eq]
      have hd1 : (bytesOf wire.val).drop i.val = [FramedChannel.Stuff.esc] := by
        rw [bytesOf_drop_cons wire.val i.val hklt, ← hb, hbv,
          List.drop_eq_nil_of_le (by rw [bytesOf_length]; omega)]
      simp only [UnstuffPost, FramedChannel.Stuff.decode]
      rw [← heq, hd1, unstuff_esc_last]
    · -- an escape followed by neither escaped value
      have hsome : o = some b := ‹o = some b›
      have hbe : b = stuff.ESC := ‹b = stuff.ESC›
      have hsome1 : o1 = some c := ‹o1 = some c›
      have hc3 : c ≠ i3 := by simpa using ‹(c != i3) = true›
      have hc4 : c ≠ i4 := by simpa using ‹(c != i4) = true›
      have hget : wire.val[i.val]? = some b := by rw [← o_post, hsome]
      have hklt : i.val < wire.val.length := by
        by_contra hcon
        rw [List.getElem?_eq_none_iff.mpr (show wire.val.length ≤ i.val by omega)] at hget
        simp at hget
      have hget1 : wire.val[i.val + 1]? = some c := by rw [← i2_post, ← o1_post, hsome1]
      have hklt2 : i.val + 1 < wire.val.length := by
        by_contra hcon
        rw [List.getElem?_eq_none_iff.mpr (show wire.val.length ≤ i.val + 1 by omega)] at hget1
        simp at hget1
      have hb : b = wire.val[i.val] := by
        rw [List.getElem?_eq_getElem hklt] at hget
        exact (Option.some.inj hget).symm
      have hcw : c = wire.val[i.val + 1] := by
        rw [List.getElem?_eq_getElem hklt2] at hget1
        exact (Option.some.inj hget1).symm
      have hbv : b.val = FramedChannel.Stuff.esc := by rw [hbe, esc_eq]
      have hcm : c.val ≠ FramedChannel.Stuff.escMarker := fun hv =>
        hc3 (Std.UScalar.eq_of_val_eq (by rw [hv, ← marker_xor, i3_post]))
      have hce : c.val ≠ FramedChannel.Stuff.escEsc := fun hv =>
        hc4 (Std.UScalar.eq_of_val_eq (by rw [hv, ← esc_xor, i4_post]))
      have hd1 : (bytesOf wire.val).drop i.val
          = FramedChannel.Stuff.esc :: c.val :: (bytesOf wire.val).drop (i.val + 2) := by
        rw [bytesOf_drop_cons wire.val i.val hklt, ← hb, hbv,
          bytesOf_drop_cons wire.val (i.val + 1) hklt2, ← hcw]
      simp only [UnstuffPost, FramedChannel.Stuff.decode]
      rw [← heq, hd1, unstuff_esc_bad c.val hcm hce]
    · -- the two-byte advance stays inside `usize`
      have hget1 : wire.val[i.val + 1]? = some c := by rw [← i2_post, ← o1_post, ‹o1 = some c›]
      have hklt2 := getElem?_some_lt hget1
      scalar_tac
    · -- an escape followed by the escaped escape byte: `esc` joins the payload
      have hbe : b = stuff.ESC := ‹b = stuff.ESC›
      have hc4eq : c = i4 :=
        Std.UScalar.eq_of_val_eq (by simpa using ‹¬(c != i4) = true›)
      have hget : wire.val[i.val]? = some b := by rw [← o_post, ‹o = some b›]
      have hklt := getElem?_some_lt hget
      have hb := eq_getElem_of_getElem? hget hklt
      have hget1 : wire.val[i.val + 1]? = some c := by rw [← i2_post, ← o1_post, ‹o1 = some c›]
      have hklt2 := getElem?_some_lt hget1
      have hcw := eq_getElem_of_getElem? hget1 hklt2
      have hi4 : i4 = stuff.ESC ^^^ stuff.XOR_MASK := Std.UScalar.eq_of_val_eq i4_post
      have hbv : b.val = FramedChannel.Stuff.esc := by rw [hbe, esc_eq]
      have hcv : c.val = FramedChannel.Stuff.escEsc := by rw [hc4eq, i4_post]; exact esc_xor
      have hi5 : i5.val = FramedChannel.Stuff.esc := by
        rw [i5_post, hc4eq, hi4]
        simp [stuff.ESC, stuff.XOR_MASK, FramedChannel.Stuff.esc]
      have hd1 : (bytesOf wire.val).drop i.val = FramedChannel.Stuff.esc ::
          FramedChannel.Stuff.escEsc :: (bytesOf wire.val).drop (i.val + 2) := by
        rw [bytesOf_drop_cons wire.val i.val hklt, ← hb, hbv,
          bytesOf_drop_cons wire.val (i.val + 1) hklt2, ← hcw, hcv]
      refine ⟨⟨by rw [i6_post]; omega, ?_, ?_⟩, by rw [i6_post]; omega⟩
      · dsimp only
        rw [out1_post, i6_post]
        simp only [List.length_append, List.length_singleton]
        omega
      · dsimp only
        rw [out1_post, bytesOf_push_reverse, hi5, i6_post, ← unstuff_esc_esc, ← hd1]
        exact heq
    · -- the two-byte advance stays inside `usize`
      have hget1 : wire.val[i.val + 1]? = some c := by rw [← i2_post, ← o1_post, ‹o1 = some c›]
      have hklt2 := getElem?_some_lt hget1
      scalar_tac
    · -- an escape followed by the escaped flag byte: `marker` joins the payload
      have hbe : b = stuff.ESC := ‹b = stuff.ESC›
      have hc3eq : c = i3 :=
        Std.UScalar.eq_of_val_eq (by simpa using ‹¬(c != i3) = true›)
      have hget : wire.val[i.val]? = some b := by rw [← o_post, ‹o = some b›]
      have hklt := getElem?_some_lt hget
      have hb := eq_getElem_of_getElem? hget hklt
      have hget1 : wire.val[i.val + 1]? = some c := by rw [← i2_post, ← o1_post, ‹o1 = some c›]
      have hklt2 := getElem?_some_lt hget1
      have hcw := eq_getElem_of_getElem? hget1 hklt2
      have hi3 : i3 = stuff.MARKER ^^^ stuff.XOR_MASK := Std.UScalar.eq_of_val_eq i3_post
      have hbv : b.val = FramedChannel.Stuff.esc := by rw [hbe, esc_eq]
      have hcv : c.val = FramedChannel.Stuff.escMarker := by rw [hc3eq, i3_post]; exact marker_xor
      have hi5 : i5.val = FramedChannel.Stuff.marker := by
        rw [i5_post, hc3eq, hi3]
        simp [stuff.MARKER, stuff.XOR_MASK, FramedChannel.Stuff.marker]
      have hd1 : (bytesOf wire.val).drop i.val = FramedChannel.Stuff.esc ::
          FramedChannel.Stuff.escMarker :: (bytesOf wire.val).drop (i.val + 2) := by
        rw [bytesOf_drop_cons wire.val i.val hklt, ← hb, hbv,
          bytesOf_drop_cons wire.val (i.val + 1) hklt2, ← hcw, hcv]
      refine ⟨⟨by rw [i6_post]; omega, ?_, ?_⟩, by rw [i6_post]; omega⟩
      · dsimp only
        rw [out1_post, i6_post]
        simp only [List.length_append, List.length_singleton]
        omega
      · dsimp only
        rw [out1_post, bytesOf_push_reverse, hi5, i6_post, ← unstuff_esc_marker, ← hd1]
        exact heq
    · -- an ordinary byte: it joins the payload unchanged
      have hbnm : b.val ≠ FramedChannel.Stuff.marker := fun hc =>
        ‹¬b = stuff.MARKER› (Std.UScalar.eq_of_val_eq (by rw [hc, marker_eq]))
      have hbne : b.val ≠ FramedChannel.Stuff.esc := fun hc =>
        ‹¬b = stuff.ESC› (Std.UScalar.eq_of_val_eq (by rw [hc, esc_eq]))
      have hget : wire.val[i.val]? = some b := by rw [← o_post, ‹o = some b›]
      have hklt := getElem?_some_lt hget
      have hb := eq_getElem_of_getElem? hget hklt
      have hd1 : (bytesOf wire.val).drop i.val
          = b.val :: (bytesOf wire.val).drop (i.val + 1) := by
        rw [bytesOf_drop_cons wire.val i.val hklt, ← hb]
      refine ⟨⟨by rw [i2_post]; omega, ?_, ?_⟩, by rw [i2_post]; omega⟩
      · dsimp only
        rw [out1_post, i2_post]
        simp only [List.length_append, List.length_singleton]
        omega
      · dsimp only
        rw [out1_post, bytesOf_push_reverse, i2_post,
          ← unstuff_plain b.val hbnm hbne, ← hd1]
        exact heq
    · -- the index reached the end of the wire without a terminating flag
      simp only [UnstuffPost]
      refine hend ?_
      simpa [Slice.len_val] using ‹¬i < wire.len›
  · exact hx

/-! ## The public decode triples

Each is a corollary of `unstuff_refines`, and each is a total triple, so each also says the extracted
`unstuff` returns -- never panics, never diverges -- on every slice. -/

/-- The extracted `unstuff` agrees with the model's `decode` on every slice. -/
theorem unstuff_refines (wire : Slice Std.U8) :
    stuff.unstuff wire ⦃ r => UnstuffPost wire r ⦄ := by
  unfold stuff.unstuff
  exact unstuff_loop_refines wire (alloc.vec.Vec.new Std.U8, 0#usize)
    ⟨by simp, by simp, by simp [bytesOf]⟩

/-- Success agreement: an extracted `Ok (out, k)` is a model success with the same payload and the
same residual bytes. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_ok_refines (wire : Slice Std.U8) :
    stuff.unstuff wire ⦃ r => ∀ out k, r = .Ok (out, k) →
      FramedChannel.Stuff.decode (bytesOf wire.val)
        = .ok (bytesOf out.val, (bytesOf wire.val).drop k.val) ⦄ := by
  apply WP.spec_mono (unstuff_refines wire)
  rintro r hr out k rfl
  simp only [UnstuffPost] at hr
  exact hr.2

/-- Completeness: a model success is an extracted `Ok` with the same payload, a consumed count
within the input, and the same residual bytes. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_complete (wire : Slice Std.U8) (p rest : List Nat)
    (h : FramedChannel.Stuff.decode (bytesOf wire.val) = .ok (p, rest)) :
    stuff.unstuff wire ⦃ r => ∃ out k, r = .Ok (out, k) ∧ bytesOf out.val = p ∧
      k.val ≤ wire.val.length ∧ (bytesOf wire.val).drop k.val = rest ⦄ := by
  apply WP.spec_mono (unstuff_refines wire)
  intro r hr
  match r, hr with
  | .Ok (out, k), hr =>
    simp only [UnstuffPost] at hr
    obtain ⟨hk, hd⟩ := hr
    rw [h] at hd
    simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hd
    exact ⟨out, k, rfl, hd.1.symm, hk, hd.2.symm⟩
  | .Err e, hr =>
    simp only [UnstuffPost] at hr
    rw [h] at hr
    exact absurd hr (by simp)

/-- Error agreement: the extracted `unstuff` returns `Err` exactly when the model refuses. Unlike
the varint codec, whose `Overlong` rejection is stricter than its model, the two agree exactly here:
there is no input the Rust refuses and the model accepts, or the other way round.
`[EXTRACTED: aeneas + bridge]` -/
theorem decode_err_iff (wire : Slice Std.U8) :
    stuff.unstuff wire ⦃ r => (∃ e, r = .Err e) ↔
      FramedChannel.Stuff.decode (bytesOf wire.val) = .fail ⦄ := by
  apply WP.spec_mono (unstuff_refines wire)
  intro r hr
  match r, hr with
  | .Ok (out, k), hr =>
    simp only [UnstuffPost] at hr
    constructor
    · rintro ⟨e, he⟩; cases he
    · intro hf
      rw [hr.2] at hf
      exact absurd hf (by simp)
  | .Err e, hr =>
    simp only [UnstuffPost] at hr
    exact ⟨fun _ => hr, fun _ => ⟨e, rfl⟩⟩

/-! ## The extracted round trip -/

/-- The extracted round trip: reading back what the extracted `encode_frame` wrote into an empty
vector returns exactly the payload, with every byte consumed. The one hypothesis is the same
`Vec::push` failure-freedom bound `encode_frame_refines` carries.
`[EXTRACTED: aeneas + bridge]` -/
theorem roundtrip_extracted (payload : Slice Std.U8)
    (h : 2 * payload.val.length + 1 ≤ Usize.max) :
    stuff.encode_frame payload (alloc.vec.Vec.new Std.U8) ⦃ v =>
      stuff.unstuff (alloc.vec.Vec.deref v) ⦃ r => ∃ out k, r = .Ok (out, k) ∧
        bytesOf out.val = bytesOf payload.val ∧ k.val = v.val.length ⦄ ⦄ := by
  apply WP.spec_mono (encode_frame_refines payload (alloc.vec.Vec.new Std.U8) (by simpa using h))
  intro v hv
  have hs : bytesOf (alloc.vec.Vec.deref v).val
      = FramedChannel.Stuff.encode (bytesOf payload.val) := by
    simpa [alloc.vec.Vec.deref, bytesOf] using hv
  apply WP.spec_mono (decode_complete _ (bytesOf payload.val) []
    (by rw [hs]; exact FramedChannel.Stuff.stuff_roundtrip (bytesOf payload.val)))
  rintro r ⟨out, k, rfl, hout, hk, hdrop⟩
  refine ⟨out, k, rfl, hout, ?_⟩
  have hdv : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hdv] at hk hdrop
  simp only [List.drop_eq_nil_iff, bytesOf_length] at hdrop
  omega

end FramedChannel.Bridge.stuff

#print axioms FramedChannel.Bridge.stuff.unstuff_nil
#print axioms FramedChannel.Bridge.stuff.unstuff_marker
#print axioms FramedChannel.Bridge.stuff.unstuff_plain
#print axioms FramedChannel.Bridge.stuff.unstuff_esc_last
#print axioms FramedChannel.Bridge.stuff.unstuff_esc_marker
#print axioms FramedChannel.Bridge.stuff.unstuff_esc_esc
#print axioms FramedChannel.Bridge.stuff.unstuff_esc_bad
#print axioms FramedChannel.Bridge.stuff.bytesOf_push_reverse
#print axioms FramedChannel.Bridge.stuff.getElem?_some_lt
#print axioms FramedChannel.Bridge.stuff.eq_getElem_of_getElem?
#print axioms FramedChannel.Bridge.stuff.unstuff_loop_refines
#print axioms FramedChannel.Bridge.stuff.unstuff_refines
#print axioms FramedChannel.Bridge.stuff.decode_ok_refines
#print axioms FramedChannel.Bridge.stuff.decode_complete
#print axioms FramedChannel.Bridge.stuff.decode_err_iff
#print axioms FramedChannel.Bridge.stuff.roundtrip_extracted
