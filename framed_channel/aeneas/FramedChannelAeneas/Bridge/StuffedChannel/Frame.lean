-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.StuffedChannel.Abstraction
import FramedChannelAeneas.Bridge.Varint.Instance
import FramedChannelAeneas.Bridge.Crc8.Instance
import FramedChannelAeneas.Bridge.Stuff.Instance
import FramedChannel.Composition.StuffedChannel.Instances

/-!
# Bridge/StuffedChannel/Frame: the extracted stuffed frame codec refines the specification's

`[EXTRACTED: aeneas + bridge]` -- the extracted `stuffed_channel.body`,
`stuffed_channel.encode_stuffed`, `stuffed_channel.parse_stuffed` and `stuffed_channel.drop_front`
(`rust/src/stuffed_channel.rs`) related to `StuffedChannel.body`, `encodeStuffed` and `parseStuffed`
(`lean/FramedChannel/Composition/StuffedChannel/Theorems.lean`).

## No component is opened

`stuffed_channel.rs` calls `encode_u32`, `decode_u32`, `crc8`, `stuff::encode_frame` and
`stuff::unstuff` directly, not through a trait, so the proofs here reach them the only way a proof
can without unfolding their loops: through the registered component refinement theorems
`Bridge.varint.encode_refines`, `Bridge.varint.decode_refines`, `Bridge.crc8.crc8_refines`,
`Bridge.stuff.encode_frame_refines` and `Bridge.stuff.unstuff_refines`, used as black-box step
specifications. No varint, CRC-8 or stuffing loop is unfolded in this file.

The model side is stated at the concrete component tags `C := Stuff.Hdlc`, `K := Crc8.Bitwise`,
because that is what the extracted code calls; the `Transparent Stuff.Hdlc Stuff.marker` instance
comes from `Composition/StuffedChannel/Instances.lean`.

## Hypotheses

`body_refines` and `encode_stuffed_refines` need their `len` argument to be the payload length
(`send` passes the value `u32::try_from` returns) and room on the output vector. Aeneas bounds a
`Vec` by `Usize.max` and panics beyond it; a body adds at most six bytes to the payload (up to five
varint length bytes and one check byte), and stuffing at most doubles the body and adds the
terminating flag, so `2 * n + 13` bytes of room always suffice.

`parse_stuffed_refines` needs no hypothesis at all -- not even an arithmetic one, because the
extracted `parse_stuffed` performs no arithmetic: every read is a `get`, and the "exactly one check
byte left" test is a length comparison against `1`. An earlier version of the Rust wrote
`rest.len() != n + 1`, which overflows a 32-bit `usize` at `u32::MAX`; writing this refinement is
what found that panic, and the Rust was corrected rather than the theorem weakened.

Its postcondition `ParsePost` is a case split rather than an equivalence in one place: a frame
declaring a length of `2 ^ 32` or more is parsed by the model (whose varint decoder is over `Nat`)
and rejected by the extraction (`Overlong`). That is the **varint layer's** divergence and the only
one: the stuffing layer contributes none, because `Bridge.stuff.decode_err_iff` is an exact iff,
where `Channel`'s parse carried `DeclaresWideLength` for the same varint reason. The disjunct is
unreachable for any wire the channel wrote, since every frame on it is `FrameOK`
(`not_declaresWide_encodeStuffed`).

`ParsePost` is typed as an Aeneas `WP.Post`, and `parse_stuffed_refines` is stated with `WP.spec`
directly rather than the `⦃ o => .. ⦄` notation, for the same reason `Bridge/Channel/Frame.lean`
does it: the named post keeps the proof's intermediate goals type-correct at `instances`
transparency, which `simp` needs to reduce the extracted `match`es.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Byte Frame FrameOK lenBytes)
open FramedChannel.StuffedChannel (body encodeStuffed parseStuffed)

/-! ## Byte and slice plumbing -/

/-- A machine byte's value is its bit vector's. -/
theorem val_eq_bv_toNat (x : Std.U8) : x.val = x.bv.toNat := rfl

/-- The value list of a dropped slice. -/
theorem slice_drop_val (s : Slice Std.U8) (k : Std.Usize) :
    (s.drop k).val = s.val.drop k.val := by simp [Slice.drop]

/-- `bytesOf` commutes with `drop`, being a map. -/
theorem bytesOf_drop (l : List Std.U8) (k : Nat) : (bytesOf l).drop k = bytesOf (l.drop k) := by
  simp [bytesOf, List.map_drop]

/-- `bytesOf` commutes with `take`, being a map. -/
theorem bytesOf_take (l : List Std.U8) (k : Nat) : (bytesOf l).take k = bytesOf (l.take k) := by
  simp [bytesOf, List.map_take]

/-- `bytesOf` preserves length. -/
theorem bytesOf_len (l : List Std.U8) : (bytesOf l).length = l.length := by simp [bytesOf]

/-! ## The model's parser, one layer at a time -/

/-- The model parser refuses a wire the stuffing codec refuses. -/
theorem parseStuffed_decode_fail (w : List Nat) (h : FramedChannel.Stuff.decode w = .fail) :
    parseStuffed (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) w = .fail := by
  simp only [parseStuffed, decode_hdlc, h]

/-- The model parser refuses a body whose length prefix does not decode. -/
theorem parseStuffed_varint_fail (w bs rest : List Nat)
    (hd : FramedChannel.Stuff.decode w = .ok (bs, rest))
    (hv : FramedChannel.Varint.decode bs = .fail) :
    parseStuffed (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) w = .fail := by
  simp only [parseStuffed, decode_hdlc, hd, hv]

/-- The model parser once both layers have succeeded: exactly the payload/check-byte split.
Rewriting with this is what lets the refinement below discharge each extracted branch without
re-deriving the `match` structure at every one. -/
theorem parseStuffed_step (w bs rest : List Nat) (n : Nat) (rem : List Nat)
    (hd : FramedChannel.Stuff.decode w = .ok (bs, rest))
    (hv : FramedChannel.Varint.decode bs = .ok (n, rem)) :
    parseStuffed (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) w =
      (match (rem.map (BitVec.ofNat 8)).drop n with
       | [c] => if ((rem.map (BitVec.ofNat 8)).take n).length = n ∧
                   c = FramedChannel.Crc8.crc8Bits ((rem.map (BitVec.ofNat 8)).take n)
                then .ok ((rem.map (BitVec.ofNat 8)).take n, rest) else .fail
       | _ => .fail) := by
  simp only [parseStuffed, decode_hdlc, hd, hv, digest_bitwise]
  rfl

/-! ## The body and the stuffed frame -/

/-- Body refinement: the extracted `body` returns exactly the specification's frame body (varint
length, payload, bitwise CRC-8) and never fails, given `len` equal to the payload length and room
for the body. `[EXTRACTED: aeneas + bridge]` -/
theorem body_refines (payload : Slice Std.U8) (len : Std.U32)
    (hlen : len.val = payload.val.length)
    (hroom : payload.val.length + 6 ≤ Usize.max) :
    stuffed_channel.body payload len
      ⦃ v => bytesOf v.val = body (K := FramedChannel.Crc8.Bitwise) (bitsOf payload.val) ⦄ := by
  have hel := FramedChannel.Varint.encode_length_le len.val (by scalar_tac)
  unfold stuffed_channel.body
  step with FramedChannel.Bridge.varint.encode_refines as ⟨out, hout⟩
  have hol : out.val.length = (FramedChannel.Varint.encode len.val).length := by
    have h := congrArg List.length hout
    simpa [FramedChannel.Bridge.varint.bytesOf] using h
  step with FramedChannel.Bridge.vec_extend_from_slice_spec core.clone.CloneU8 (fun _ => rfl)
    as ⟨out1, hout1⟩
  step with FramedChannel.Bridge.crc8.crc8_refines as ⟨c, hc⟩
  step*
  rw [v_post, hout1]
  have hbo : bytesOf out.val = FramedChannel.Varint.encode len.val := by
    simpa [FramedChannel.Bridge.varint.bytesOf, bytesOf] using hout
  have hlp : (bitsOf payload.val).length = payload.val.length := by simp [bitsOf]
  rw [body_eq, hlp, ← hlen]
  simp only [List.map_append, List.map_cons, List.map_nil, ← bytesOf_eq_map_toNat,
    FramedChannel.Bridge.stuff.bytesOf_append, hbo, List.append_assoc]
  simp only [bytesOf, List.map_cons, List.map_nil, val_eq_bv_toNat, hc]

/-- Framing refinement: the extracted `encode_stuffed` appends exactly the specification's stuffed
frame -- the body, byte-stuffed and terminated by the flag -- to the output, and never fails, given
`len` equal to the payload length and room for the frame. `[EXTRACTED: aeneas + bridge]` -/
theorem encode_stuffed_refines (payload : Slice Std.U8) (len : Std.U32)
    (out : alloc.vec.Vec Std.U8) (hlen : len.val = payload.val.length)
    (hroom : out.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.encode_stuffed payload len out
      ⦃ v => bytesOf v.val
        = bytesOf out.val ++ encodeStuffed (C := FramedChannel.Stuff.Hdlc)
            (K := FramedChannel.Crc8.Bitwise) (bitsOf payload.val) ⦄ := by
  have hlp : (bitsOf payload.val).length = payload.val.length := by simp [bitsOf]
  have hbl : (body (K := FramedChannel.Crc8.Bitwise) (bitsOf payload.val)).length
      ≤ payload.val.length + 6 := by
    have := body_length_le (bitsOf payload.val) (by simp only [FrameOK, hlp]; scalar_tac)
    omega
  unfold stuffed_channel.encode_stuffed
  step with body_refines payload len hlen (by omega) as ⟨frame, hframe⟩
  have hfl : frame.val.length ≤ payload.val.length + 6 := by
    have h := congrArg List.length hframe
    rw [bytesOf_len] at h
    omega
  have hderef : (alloc.vec.Vec.deref frame).val = frame.val := by
    simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  apply WP.spec_mono (FramedChannel.Bridge.stuff.encode_frame_refines
    (alloc.vec.Vec.deref frame) out (by rw [hderef]; omega))
  intro v hv
  rw [hv, hderef, hframe, encodeStuffed_eq]

/-- `drop_front` drops exactly `n` bytes (all of them when `n` exceeds the length), and never
fails. -/
theorem drop_front_refines (b : Slice Std.U8) (n : Std.Usize) :
    stuffed_channel.drop_front b n ⦃ v => bytesOf v.val = (bytesOf b.val).drop n.val ⦄ := by
  unfold stuffed_channel.drop_front
  obtain ⟨o, ho, hop⟩ := (WP.spec_equiv_exists _ _).mp
    (FramedChannel.Bridge.slice_get_range_from_spec b { start := n })
  rw [ho]
  simp only [bind_tc_ok]
  by_cases hn : n.val ≤ b.val.length
  · rw [if_pos hn] at hop
    subst hop
    simp only
    apply WP.spec_mono (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 _ (fun _ _ => rfl))
    intro v hv
    have hvv : v.val = (b.drop n).val := by rw [hv]; rfl
    simp [hvv, bytesOf_drop, slice_drop_val]
  · rw [if_neg hn] at hop
    subst hop
    simp only [WP.spec_ok]
    rw [bytesOf_drop, List.drop_eq_nil_of_le (by omega)]
    simp [bytesOf]

/-! ## The parser -/

/-- Parser refinement: the extracted `parse_stuffed` never fails, and its result is related to the
specification's `parseStuffed` of the same bytes by `ParsePost`. The stuffing, the varint length and
the CRC-8 are reached only through `unstuff_refines`, `decode_refines` and `crc8_refines`; no loop of
any of the three is unfolded here. `[EXTRACTED: aeneas + bridge]` -/
theorem parse_stuffed_refines (wire : Slice Std.U8) :
    WP.spec (stuffed_channel.parse_stuffed wire) (ParsePost (bytesOf wire.val)) := by
  unfold stuffed_channel.parse_stuffed
  step with FramedChannel.Bridge.stuff.unstuff_refines as ⟨r, hr⟩
  rcases r with ⟨frame, used⟩ | e
  · simp only [FramedChannel.Bridge.stuff.UnstuffPost] at hr
    obtain ⟨hused, hdec⟩ := hr
    have hderef : (alloc.vec.Vec.deref frame).val = frame.val := by
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
    step*
    step with FramedChannel.Bridge.varint.decode_refines as ⟨r1, hr1⟩
    rcases r1 with ⟨n, consumed⟩ | e1
    · simp only [FramedChannel.Bridge.varint.DecPost] at hr1
      obtain ⟨hcons, hvd⟩ := hr1
      rw [hderef, ← bytesOf_eq_varint_bytesOf, bytesOf_len] at hcons
      rw [hderef, ← bytesOf_eq_varint_bytesOf] at hvd
      have hmodel := parseStuffed_step (bytesOf wire.val) (bytesOf frame.val)
        ((bytesOf wire.val).drop used.val) n.val ((bytesOf frame.val).drop consumed.val) hdec hvd
      have hcast : (UScalar.cast UScalarTy.Usize n).val = n.val := by
        simp only [UScalar.cast_val_eq]
        apply Nat.mod_eq_of_lt
        have h1 : n.val < 2 ^ 32 := n.hBounds
        have h2 : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
          apply Nat.pow_le_pow_right (by omega)
          rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
        omega
      have hVal : ((alloc.vec.Vec.deref frame).drop consumed).val
          = frame.val.drop consumed.val := by rw [slice_drop_val, hderef]
      rw [bytesOf_drop, ← hVal, map_ofNat_bytesOf] at hmodel
      step*
      -- (1) something other than exactly one check byte remains
      · have hcf : cf = core.ops.control_flow.ControlFlow.Continue val := ‹cf = core.ops.control_flow.ControlFlow.Continue val›
        have hcf2 : cf2 = core.ops.control_flow.ControlFlow.Continue val2 := ‹cf2 = core.ops.control_flow.ControlFlow.Continue val2›
        have hne : (val2.len != 1#usize) = true := ‹(val2.len != 1#usize) = true›
        have hoval : o = some ((alloc.vec.Vec.deref frame).drop consumed) := by
          rw [o_post, if_pos (by rw [hderef]; exact hcons)]
        have hn1 : n1.val = n.val := by rw [n1_post]; exact hcast
        have hval : val = (alloc.vec.Vec.deref frame).drop consumed := by
          rw [hoval] at cf_post; simp only at cf_post
          rw [cf_post] at hcf; injection hcf with h; exact h.symm
        have hn1le : n1.val ≤ val.val.length := by
          by_contra hcon
          rw [if_neg hcon] at o2_post
          rw [o2_post] at cf2_post; simp only at cf2_post
          rw [cf2_post] at hcf2; cases hcf2
        have hval2 : val2 = val.drop n1 := by
          rw [if_pos hn1le] at o2_post
          rw [o2_post] at cf2_post; simp only at cf2_post
          rw [cf2_post] at hcf2; injection hcf2 with h; exact h.symm
        have hlen2 : val2.val.length = val.val.length - n.val := by
          rw [hval2, slice_drop_val, List.length_drop, hn1]
        have hne' : val.val.length - n.val ≠ 1 := by
          intro h
          have : val2.len = 1#usize := by
            apply UScalar.eq_of_val_eq; simp only [Slice.len_val, hlen2, h]; rfl
          simp [this] at hne
        rw [← hval] at hmodel
        simp only [WP.spec_ok, ParsePost]
        left
        rw [hmodel]
        rcases hl : (bitsOf val.val).drop n.val with _ | ⟨c0, tl⟩
        · simp only [hl]
        · cases tl with
          | nil =>
            exfalso
            have := congrArg List.length hl
            simp only [bitsOf, List.length_drop, List.length_map, List.length_cons,
              List.length_nil] at this
            exact hne' this
          | cons c1 tl' => simp only [hl]
      -- (2) the success path
      · have hcf : cf = core.ops.control_flow.ControlFlow.Continue val := ‹cf = core.ops.control_flow.ControlFlow.Continue val›
        have hcf1 : cf1 = core.ops.control_flow.ControlFlow.Continue val1 := ‹cf1 = core.ops.control_flow.ControlFlow.Continue val1›
        have hcf2 : cf2 = core.ops.control_flow.ControlFlow.Continue val2 := ‹cf2 = core.ops.control_flow.ControlFlow.Continue val2›
        have hone : ¬(val2.len != 1#usize) = true := ‹¬(val2.len != 1#usize) = true›
        have hcf3 : cf3 = core.ops.control_flow.ControlFlow.Continue val3 := ‹cf3 = core.ops.control_flow.ControlFlow.Continue val3›
        have hoval : o = some ((alloc.vec.Vec.deref frame).drop consumed) := by
          rw [o_post, if_pos (by rw [hderef]; exact hcons)]
        have hn1 : n1.val = n.val := by rw [n1_post]; exact hcast
        have hval : val = (alloc.vec.Vec.deref frame).drop consumed := by
          rw [hoval] at cf_post; simp only at cf_post
          rw [cf_post] at hcf; injection hcf with h; exact h.symm
        have hn1le : n1.val ≤ val.val.length := by
          by_contra hcon
          rw [if_neg hcon] at o2_post
          rw [o2_post] at cf2_post; simp only at cf2_post
          rw [cf2_post] at hcf2; cases hcf2
        have hval2 : val2 = val.drop n1 := by
          rw [if_pos hn1le] at o2_post
          rw [o2_post] at cf2_post; simp only at cf2_post
          rw [cf2_post] at hcf2; injection hcf2 with h; exact h.symm
        have hlen2 : val2.val.length = val.val.length - n.val := by
          rw [hval2, slice_drop_val, List.length_drop, hn1]
        have hone' : val.val.length - n.val = 1 := by
          have h1 : val2.val.length = 1 := by simpa using hone
          omega
        have hlt : n.val < val.val.length := by omega
        -- the payload slice
        obtain ⟨s', hs'eq, hs'⟩ := o1_post (by omega)
        have hval1 : val1 = s' := by
          rw [hs'eq] at cf1_post; simp only at cf1_post
          rw [cf1_post] at hcf1; injection hcf1 with h; exact h.symm
        have hpv : payload.val = val.val.take n.val := by
          rw [hn1] at hs'
          rw [← hs', ← hval1, val1_post]
          rfl
        -- the check byte
        have hval3 : val.val[n.val]? = some val3 := by
          rw [← hn1, ← o3_post]
          rcases o3 with _ | c
          · rw [cf3_post] at hcf3; simp only at hcf3; cases hcf3
          · rw [cf3_post] at hcf3; simp only at hcf3; injection hcf3 with h; rw [h]
        have hval3' : val3 = val.val[n.val]'hlt := by
          rw [List.getElem?_eq_getElem hlt] at hval3
          exact (Option.some.inj hval3).symm
        have hpderef : (alloc.vec.Vec.deref payload).val = payload.val := by
          simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
        step with FramedChannel.Bridge.crc8.crc8_refines as ⟨i1, hi1⟩
        rw [hpderef] at hi1
        -- fold the model's take/drop
        have htake : (bitsOf val.val).take n.val = bitsOf payload.val := by
          simp only [bitsOf, ← List.map_take, hpv]
        have hdrop : (bitsOf val.val).drop n.val = [val3.bv] := by
          simp only [bitsOf, ← List.map_drop]
          rw [List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega), hval3']
          rfl
        have hplen : (bitsOf payload.val).length = n.val := by
          simp only [bitsOf, List.length_map, hpv, List.length_take]; omega
        rw [← hval, hdrop, htake] at hmodel
        by_cases hchk : val3 = i1
        · rw [show (val3 != i1) = false from by simp [hchk]]
          simp only [Bool.false_eq_true, if_false, WP.spec_ok, ParsePost]
          refine ⟨by rw [bytesOf_len]; exact hused, ?_⟩
          rw [hmodel, hplen, hchk, hi1]
          simp
        · rw [show (val3 != i1) = true from by simp [hchk]]
          simp only [if_true, WP.spec_ok, ParsePost]
          left
          rw [hmodel, hplen]
          simp only [true_and]
          rw [if_neg]
          intro h
          apply hchk
          apply UScalar.eq_of_val_eq
          have : val3.bv = i1.bv := by rw [h, hi1]
          exact congrArg UScalar.val ((UScalar.eq_equiv_bv_eq _ _).mpr this)
      -- (3) the check byte's `get` missed: impossible
      · exfalso
        have hcf : cf = core.ops.control_flow.ControlFlow.Continue val := ‹cf = core.ops.control_flow.ControlFlow.Continue val›
        have hcf2 : cf2 = core.ops.control_flow.ControlFlow.Continue val2 := ‹cf2 = core.ops.control_flow.ControlFlow.Continue val2›
        have hone : ¬(val2.len != 1#usize) = true := ‹¬(val2.len != 1#usize) = true›
        have hcf3 : cf3 = core.ops.control_flow.ControlFlow.Break residual := ‹cf3 = core.ops.control_flow.ControlFlow.Break residual›

        have hoval : o = some ((alloc.vec.Vec.deref frame).drop consumed) := by
          rw [o_post, if_pos (by rw [hderef]; exact hcons)]
        have hn1 : n1.val = n.val := by rw [n1_post]; exact hcast
        have hval : val = (alloc.vec.Vec.deref frame).drop consumed := by
          rw [hoval] at cf_post; simp only at cf_post
          rw [cf_post] at hcf; injection hcf with h; exact h.symm
        have hn1le : n1.val ≤ val.val.length := by
          by_contra hcon
          rw [if_neg hcon] at o2_post
          rw [o2_post] at cf2_post; simp only at cf2_post
          rw [cf2_post] at hcf2; cases hcf2
        have hval2 : val2 = val.drop n1 := by
          rw [if_pos hn1le] at o2_post
          rw [o2_post] at cf2_post; simp only at cf2_post
          rw [cf2_post] at hcf2; injection hcf2 with h; exact h.symm
        have hlen2 : val2.val.length = val.val.length - n.val := by
          rw [hval2, slice_drop_val, List.length_drop, hn1]
        have hone' : val.val.length - n.val = 1 := by
          have h1 : val2.val.length = 1 := by simpa using hone
          omega
        have hlt : n.val < val.val.length := by omega
        rw [hn1, List.getElem?_eq_getElem hlt] at o3_post
        rw [o3_post] at cf3_post; simp only at cf3_post
        rw [cf3_post] at hcf3; cases hcf3
      -- (4) the payload's `get` missed: the declared length exceeds the body
      · have hcf : cf = core.ops.control_flow.ControlFlow.Continue val := ‹cf = core.ops.control_flow.ControlFlow.Continue val›
        have hcf1 : cf1 = core.ops.control_flow.ControlFlow.Break residual := ‹cf1 = core.ops.control_flow.ControlFlow.Break residual›
        have hoval : o = some ((alloc.vec.Vec.deref frame).drop consumed) := by
          rw [o_post, if_pos (by rw [hderef]; exact hcons)]
        have hn1 : n1.val = n.val := by rw [n1_post]; exact hcast
        have hval : val = (alloc.vec.Vec.deref frame).drop consumed := by
          rw [hoval] at cf_post; simp only at cf_post
          rw [cf_post] at hcf; injection hcf with h; exact h.symm
        have hno : ¬ n1.val ≤ val.val.length := by
          intro hle
          obtain ⟨s', hs'eq, -⟩ := o1_post hle
          rw [hs'eq] at cf1_post; simp only at cf1_post
          rw [cf1_post] at hcf1; cases hcf1
        rw [hn1] at hno
        simp only [
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
        have hres : residual = none := by
          rcases residual with _ | x
          · rfl
          · cases x
        rw [hres]
        simp only [WP.spec_ok, ParsePost]
        left
        rw [← hval] at hmodel
        rw [hmodel, List.drop_eq_nil_of_le (by simp only [bitsOf, List.length_map]; omega)]
    · simp only [FramedChannel.Bridge.varint.DecPost] at hr1
      rw [hderef, ← bytesOf_eq_varint_bytesOf] at hr1
      simp only [WP.spec_ok, ParsePost]
      rcases hr1 with hf | ⟨n, rem, hd, hn⟩
      · exact Or.inl (parseStuffed_varint_fail _ _ _ hdec hf)
      · exact Or.inr ⟨_, _, n, rem, hdec, hd, hn⟩
  · simp only [FramedChannel.Bridge.stuff.UnstuffPost] at hr
    simp only [WP.spec_ok, ParsePost]
    exact Or.inl (parseStuffed_decode_fail _ hr)

/-! ## The extracted round trip -/

/-- The length prefix of a frame body decodes to the payload length. -/
theorem decode_body (p : Frame) (hp : FrameOK p) :
    FramedChannel.Varint.decode (body (K := FramedChannel.Crc8.Bitwise) p)
      = .ok (p.length, (p ++ [FramedChannel.Crc8.crc8Bits p]).map BitVec.toNat) := by
  have hv := FramedChannel.Varint.varint_roundtrip p.length (by simpa [FrameOK] using hp)
  have hd := FramedChannel.Channel.decodeF_append 5 1 0 p.length
    (FramedChannel.Varint.encode p.length)
    ((p ++ [FramedChannel.Crc8.crc8Bits p]).map BitVec.toNat) hv
  rw [body_eq]
  simp only [FramedChannel.Varint.decode] at hd ⊢
  exact hd

/-- A frame the channel accepts never declares a wide length, so `ParsePost`'s divergence disjunct
is unreachable on any wire this channel wrote. -/
theorem not_declaresWide_encodeStuffed (p : Frame) (rest : List Nat) (hp : FrameOK p) :
    ¬ DeclaresWideLength (encodeStuffed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) p ++ rest) := by
  rintro ⟨bs, rest', n, rem, hd, hv, hn⟩
  rw [encodeStuffed_eq, ← encode_hdlc] at hd
  rw [← decode_hdlc, FramedChannel.StuffedChannel.Transparent.decode_append
    (C := FramedChannel.Stuff.Hdlc) (flag := FramedChannel.Stuff.marker)
    (body (K := FramedChannel.Crc8.Bitwise) p) rest] at hd
  simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hd
  obtain ⟨hbs, -⟩ := hd
  rw [← hbs, decode_body p hp] at hv
  simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hv
  simp only [FrameOK] at hp
  omega

/-- The extracted stuffed round trip: on any wire that starts with the specification's stuffed
encoding of a payload `p` whose length fits a `u32`, the extracted parser returns exactly `p` and
consumes exactly the frame. The only hypothesis is the length bound (`send` refuses longer
payloads). `[EXTRACTED: aeneas + bridge]` -/
theorem parse_stuffed_encode_stuffed_extracted (w : Slice Std.U8) (p : Frame) (rest : List Nat)
    (hp : p.length ≤ U32.max)
    (hw : bytesOf w.val = encodeStuffed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) p ++ rest) :
    stuffed_channel.parse_stuffed w
      ⦃ o => ∃ v used, o = some (v, used) ∧ bitsOf v.val = p ∧
        used.val = (encodeStuffed (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) p).length ⦄ := by
  have hp' : p.length < 2 ^ 32 := by scalar_tac
  have hok : FrameOK p := hp'
  have hps := FramedChannel.StuffedChannel.parseStuffed_encodeStuffed
    (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
    FramedChannel.Stuff.marker p rest hp'
  apply WP.spec_mono (parse_stuffed_refines w)
  intro o ho
  rcases o with _ | ⟨v, used⟩
  · simp only [ParsePost] at ho
    rcases ho with hf | hwide
    · rw [hw, hps] at hf; cases hf
    · rw [hw] at hwide
      exact absurd hwide (not_declaresWide_encodeStuffed p rest hok)
  · simp only [ParsePost] at ho
    obtain ⟨hle, hpar⟩ := ho
    rw [hw] at hpar hle
    rw [hps] at hpar
    simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hpar
    obtain ⟨h1, h2⟩ := hpar
    refine ⟨v, used, rfl, h1.symm, ?_⟩
    have h3 := congrArg List.length h2
    simp only [List.length_drop, List.length_append] at h3 hle
    omega

end FramedChannel.Bridge.stuffed_channel

#print axioms FramedChannel.Bridge.stuffed_channel.val_eq_bv_toNat
#print axioms FramedChannel.Bridge.stuffed_channel.slice_drop_val
#print axioms FramedChannel.Bridge.stuffed_channel.bytesOf_drop
#print axioms FramedChannel.Bridge.stuffed_channel.bytesOf_take
#print axioms FramedChannel.Bridge.stuffed_channel.bytesOf_len
#print axioms FramedChannel.Bridge.stuffed_channel.parseStuffed_decode_fail
#print axioms FramedChannel.Bridge.stuffed_channel.parseStuffed_varint_fail
#print axioms FramedChannel.Bridge.stuffed_channel.parseStuffed_step
#print axioms FramedChannel.Bridge.stuffed_channel.body_refines
#print axioms FramedChannel.Bridge.stuffed_channel.encode_stuffed_refines
#print axioms FramedChannel.Bridge.stuffed_channel.drop_front_refines
#print axioms FramedChannel.Bridge.stuffed_channel.parse_stuffed_refines
#print axioms FramedChannel.Bridge.stuffed_channel.decode_body
#print axioms FramedChannel.Bridge.stuffed_channel.not_declaresWide_encodeStuffed
#print axioms FramedChannel.Bridge.stuffed_channel.parse_stuffed_encode_stuffed_extracted
