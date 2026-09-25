-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.Stuff.Defs
import FramedChannel.Model.Stuff.Theorems

/-!
# Bridge/Stuff/Stuff: the extracted `stuff` and `encode_frame` refine the model's `stuff`/`encode`

`[EXTRACTED: aeneas + bridge]` -- `stuff_refines` proves that the Charon/Aeneas extraction of
`rust/src/stuff.rs`'s `stuff` (`Extracted/Funs.lean`, a `loop` over the payload indices) appends to
its output vector exactly the bytes `FramedChannel.Stuff.stuff` computes, read through `bytesOf`,
and `encode_frame_refines` adds the terminating flag to reach the model's `encode`.

The triples are total correctness, so they also rule out every failure of the extracted code: the
`u8` xor with `XOR_MASK` (total), the `usize` increment (bounded by the slice length) and each
`Vec::push`, whose overflow obligation is the one hypothesis. That hypothesis is
`out.length + 2 * payload.length <= usize::MAX` -- the analogue of `varint.encode_refines`'s
`out.length + 5 <= Usize.max`, with `2 * payload.length` rather than a constant because stuffing
expands with its input (the model's `stuff_length_le` is the same bound). It is carried as an
explicit hypothesis rather than hidden by strengthening the claim.

The proof is one application of Aeneas's `loop.spec_decr_nat` with measure `payload.len() - i` and
the invariant `StuffInv`: after reaching index `k`, at most `2 * k` bytes have been pushed, and the
bytes pushed so far followed by the model's `stuff` of the *remaining* payload are the full model
encoding. Phrasing the invariant on the remaining suffix (`drop k`) rather than the consumed prefix
is what lets the model's own defining equation `stuff (b :: bs) = stuffByte b ++ stuff bs` discharge
each step, with no `stuff (xs ++ ys)` distribution lemma needed.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuff
open framed_channel

/-! ## The extracted constants, as `Nat` values

The extraction emits each `pub const` as an `irreducible` definition, so its value is read off once
here rather than unfolded at every use. -/

theorem MARKER_val : stuff.MARKER.val = 126 := by simp [stuff.MARKER]

theorem ESC_val : stuff.ESC.val = 125 := by simp [stuff.ESC]

/-- The model's `marker` is the extracted `MARKER`'s value. -/
theorem marker_eq : FramedChannel.Stuff.marker = stuff.MARKER.val := by
  rw [MARKER_val]; rfl

/-- The model's `esc` is the extracted `ESC`'s value. -/
theorem esc_eq : FramedChannel.Stuff.esc = stuff.ESC.val := by
  rw [ESC_val]; rfl

/-- The escape of the flag byte, as the machine computes it. -/
theorem marker_xor : (stuff.MARKER ^^^ stuff.XOR_MASK).val = FramedChannel.Stuff.escMarker := by
  simp [stuff.MARKER, stuff.XOR_MASK, FramedChannel.Stuff.escMarker]

/-- The escape of the escape byte, as the machine computes it. -/
theorem esc_xor : (stuff.ESC ^^^ stuff.XOR_MASK).val = FramedChannel.Stuff.escEsc := by
  simp [stuff.ESC, stuff.XOR_MASK, FramedChannel.Stuff.escEsc]

/-! ## Abstraction lemmas -/

theorem stuff_nil : FramedChannel.Stuff.stuff [] = [] := rfl

theorem bytesOf_length (l : List Std.U8) : (bytesOf l).length = l.length := by simp [bytesOf]

theorem bytesOf_append (a b : List Std.U8) : bytesOf (a ++ b) = bytesOf a ++ bytesOf b := by
  simp [bytesOf]

/-- The abstracted payload's suffix at `k`, peeled: the byte at `k` followed by the rest. -/
theorem bytesOf_drop_cons (l : List Std.U8) (k : Nat) (hk : k < l.length) :
    (bytesOf l).drop k = (l[k]).val :: (bytesOf l).drop (k + 1) := by
  have hk' : k < (bytesOf l).length := by rw [bytesOf_length]; exact hk
  rw [List.drop_eq_getElem_cons hk']
  congr 1
  simp [bytesOf]

/-! ## The loop invariant -/

/-- The loop invariant, over the loop state `(output, index)`. After reaching index `k`: at most
`2 * k` bytes have been pushed, and the bytes pushed so far followed by the model's `stuff` of the
payload's remaining suffix are the full model encoding. -/
def StuffInv (payload : Slice Std.U8) (out0 : alloc.vec.Vec Std.U8)
    (x : alloc.vec.Vec Std.U8 × Std.Usize) : Prop :=
  ∃ k : Nat, k ≤ payload.val.length ∧ x.2.val = k ∧
    x.1.val.length ≤ out0.val.length + 2 * k ∧
    bytesOf x.1.val ++ FramedChannel.Stuff.stuff ((bytesOf payload.val).drop k) =
      bytesOf out0.val ++ FramedChannel.Stuff.stuff (bytesOf payload.val)

/-- The loop lemma: from any state satisfying `StuffInv`, the extracted loop ends with the model's
full stuffing appended. -/
theorem stuff_loop_refines (payload : Slice Std.U8) (out0 : alloc.vec.Vec Std.U8)
    (h : out0.val.length + 2 * payload.val.length ≤ Usize.max)
    (x : alloc.vec.Vec Std.U8 × Std.Usize) (hx : StuffInv payload out0 x) :
    stuff.stuff_loop payload x.1 x.2
      ⦃ v => bytesOf v.val =
        bytesOf out0.val ++ FramedChannel.Stuff.stuff (bytesOf payload.val) ⦄ := by
  unfold stuff.stuff_loop
  apply loop.spec_decr_nat
    (measure := fun (x : alloc.vec.Vec Std.U8 × Std.Usize) => payload.val.length - x.2.val)
    (inv := StuffInv payload out0)
  · rintro ⟨out, i⟩ ⟨k, hklen, hik, hlen, heq⟩
    simp only at hik hlen heq
    subst hik
    have hfin : payload.val.length ≤ i.val →
        bytesOf out.val = bytesOf out0.val ++ FramedChannel.Stuff.stuff (bytesOf payload.val) := by
      intro hk
      rw [List.drop_eq_nil_of_le (by rw [bytesOf_length]; omega), stuff_nil,
        List.append_nil] at heq
      exact heq
    unfold stuff.stuff_loop.body
    step*
    · -- `get` returned `none`: only reachable past the end of the payload
      rename_i hnone
      refine hfin ?_
      rw [hnone] at o_post
      simp at o_post
      omega
    · -- a payload byte was read: the three branches of `stuffByte`
      rename_i hsome
      have hget : payload.val[i.val]? = some b := by rw [← o_post, hsome]
      have hklt : i.val < payload.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none_iff.mpr (show payload.val.length ≤ i.val by omega)] at hget
        simp at hget
      have hb : b = payload.val[i.val] := by
        rw [List.getElem?_eq_getElem hklt] at hget
        exact (Option.some.inj hget).symm
      have hdrop : (bytesOf payload.val).drop i.val =
          b.val :: (bytesOf payload.val).drop (i.val + 1) := by
        rw [bytesOf_drop_cons payload.val i.val hklt, hb]
      -- peel the model's own defining equation off the remaining suffix
      rw [hdrop, FramedChannel.Stuff.stuff, ← List.append_assoc] at heq
      have hb2 : out.val.length + 2 ≤ Usize.max := by omega
      split
      · -- the flag byte: `esc` then `escMarker` go out
        rename_i hbm
        step*
        · scalar_tac
        · -- the two-push output, with the intermediate vector reached by `assumption`
          have hout1v : out1.val = out.val ++ [stuff.ESC, x] := by
            rw [out1_post, show out.val ++ [stuff.ESC, x] = (out.val ++ [stuff.ESC]) ++ [x] by simp]
            exact congrArg (· ++ [x]) (by assumption)
          have hbv : b.val = FramedChannel.Stuff.marker := by rw [hbm, marker_eq]
          have hxv : x.val = FramedChannel.Stuff.escMarker := by rw [x_post, hbm]; exact marker_xor
          have hout1 : bytesOf out1.val
              = bytesOf out.val ++ FramedChannel.Stuff.stuffByte b.val := by
            rw [hbv, FramedChannel.Stuff.stuffByte_marker, hout1v]
            simp [bytesOf, hxv, ESC_val, FramedChannel.Stuff.esc]
          have hlen1 : out1.val.length = out.val.length + 2 := by rw [hout1v]; simp
          refine ⟨⟨i.val + 1, by omega, i2_post, by dsimp only; omega, ?_⟩, by omega⟩
          rw [hout1]
          exact heq
      · split
        · -- the escape byte: `esc` then `escEsc` go out
          rename_i hbm hbe
          step*
          · scalar_tac
          · have hout1v : out1.val = out.val ++ [stuff.ESC, x] := by
              rw [out1_post,
                show out.val ++ [stuff.ESC, x] = (out.val ++ [stuff.ESC]) ++ [x] by simp]
              exact congrArg (· ++ [x]) (by assumption)
            have hbv : b.val = FramedChannel.Stuff.esc := by rw [hbe, esc_eq]
            have hxv : x.val = FramedChannel.Stuff.escEsc := by rw [x_post, hbe]; exact esc_xor
            have hout1 : bytesOf out1.val
                = bytesOf out.val ++ FramedChannel.Stuff.stuffByte b.val := by
              rw [hbv, FramedChannel.Stuff.stuffByte_esc, hout1v]
              simp [bytesOf, hxv, ESC_val, FramedChannel.Stuff.esc]
            have hlen1 : out1.val.length = out.val.length + 2 := by rw [hout1v]; simp
            refine ⟨⟨i.val + 1, by omega, i2_post, by dsimp only; omega, ?_⟩, by omega⟩
            rw [hout1]
            exact heq
        · -- an ordinary byte: copied through unchanged
          rename_i hbm hbe
          have hbnm : b.val ≠ FramedChannel.Stuff.marker := fun hc =>
            hbm (Std.UScalar.eq_of_val_eq (by rw [hc, marker_eq]))
          have hbne : b.val ≠ FramedChannel.Stuff.esc := fun hc =>
            hbe (Std.UScalar.eq_of_val_eq (by rw [hc, esc_eq]))
          step*
          have hout1 : bytesOf out1.val
              = bytesOf out.val ++ FramedChannel.Stuff.stuffByte b.val := by
            rw [FramedChannel.Stuff.stuffByte_other b.val hbnm hbne, out1_post]
            simp [bytesOf]
          have hlen1 : out1.val.length = out.val.length + 1 := by rw [out1_post]; simp
          refine ⟨⟨i.val + 1, by omega, i2_post, by dsimp only; omega, ?_⟩, by omega⟩
          rw [hout1]
          exact heq
  · exact hx

/-! ## The public refinement triples -/

/-- Stuffing refinement: the extracted `stuff` appends exactly the model's stuffed payload, and
never fails, given room for two bytes per input byte. `[EXTRACTED: aeneas + bridge]` -/
theorem stuff_refines (payload : Slice Std.U8) (out : alloc.vec.Vec Std.U8)
    (h : out.val.length + 2 * payload.val.length ≤ Usize.max) :
    stuff.stuff payload out
      ⦃ v => bytesOf v.val =
        bytesOf out.val ++ FramedChannel.Stuff.stuff (bytesOf payload.val) ⦄ := by
  unfold stuff.stuff
  exact stuff_loop_refines payload out h (out, 0#usize)
    ⟨0, by omega, rfl, by dsimp only; omega, by simp⟩

/-- The stuffed payload is never longer than twice the payload, so the vector the extracted `stuff`
returns still has room for the terminating flag. -/
theorem stuff_out_length (payload : Slice Std.U8) (out v : alloc.vec.Vec Std.U8)
    (hbytes : bytesOf v.val = bytesOf out.val ++ FramedChannel.Stuff.stuff (bytesOf payload.val)) :
    v.val.length ≤ out.val.length + 2 * payload.val.length := by
  have hl := congrArg List.length hbytes
  rw [List.length_append, bytesOf_length, bytesOf_length] at hl
  have := FramedChannel.Stuff.stuff_length_le (bytesOf payload.val)
  rw [bytesOf_length] at this
  omega

/-- Framing refinement: the extracted `encode_frame` appends exactly the model's `encode` -- the
stuffed payload followed by the terminating flag -- and never fails, given room for the flag as
well. `[EXTRACTED: aeneas + bridge]` -/
theorem encode_frame_refines (payload : Slice Std.U8) (out : alloc.vec.Vec Std.U8)
    (h : out.val.length + 2 * payload.val.length + 1 ≤ Usize.max) :
    stuff.encode_frame payload out
      ⦃ v => bytesOf v.val =
        bytesOf out.val ++ FramedChannel.Stuff.encode (bytesOf payload.val) ⦄ := by
  have h' : out.val.length + 2 * payload.val.length ≤ Usize.max := by omega
  obtain ⟨w, hw, hbytes⟩ := (WP.spec_equiv_exists _ _).mp (stuff_refines payload out h')
  have hwlen : w.val.length ≤ out.val.length + 2 * payload.val.length :=
    stuff_out_length payload out w hbytes
  unfold stuff.encode_frame
  rw [hw]
  step*
  rw [v_post, FramedChannel.Stuff.encode, bytesOf_append, hbytes, List.append_assoc]
  simp [bytesOf, MARKER_val, FramedChannel.Stuff.marker]

end FramedChannel.Bridge.stuff

#print axioms FramedChannel.Bridge.stuff.MARKER_val
#print axioms FramedChannel.Bridge.stuff.ESC_val
#print axioms FramedChannel.Bridge.stuff.marker_eq
#print axioms FramedChannel.Bridge.stuff.esc_eq
#print axioms FramedChannel.Bridge.stuff.marker_xor
#print axioms FramedChannel.Bridge.stuff.esc_xor
#print axioms FramedChannel.Bridge.stuff.stuff_nil
#print axioms FramedChannel.Bridge.stuff.bytesOf_length
#print axioms FramedChannel.Bridge.stuff.bytesOf_append
#print axioms FramedChannel.Bridge.stuff.bytesOf_drop_cons
#print axioms FramedChannel.Bridge.stuff.stuff_loop_refines
#print axioms FramedChannel.Bridge.stuff.stuff_refines
#print axioms FramedChannel.Bridge.stuff.stuff_out_length
#print axioms FramedChannel.Bridge.stuff.encode_frame_refines
