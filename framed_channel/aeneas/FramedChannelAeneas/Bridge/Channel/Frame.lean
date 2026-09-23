-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.Channel.Abstraction
import FramedChannelAeneas.Bridge.Varint.Instance
import FramedChannelAeneas.Bridge.Crc8.Instance

/-!
# Bridge/Channel/Frame: the extracted frame codec refines the specification's

`[EXTRACTED: aeneas + bridge]` -- the extracted `channel.encode_frame` and
`channel.parse_frame` (`rust/src/channel.rs`) related to `Channel.encodeFrame` and
`Channel.parseFrame` (`lean/FramedChannel/Composition/Channel/Theorems.lean`).

## No component is opened

`channel.rs` calls `encode_u32`, `decode_u32` and `crc8` directly, not through a trait, so the
proofs here reach them the only way a proof can without unfolding their loops: through the
registered component refinement theorems `Bridge.varint.encode_refines`,
`Bridge.varint.decode_refines` and `Bridge.crc8.crc8_refines`, used as black-box step
specifications (`step with ... as ⟨..⟩`). No varint or CRC-8 loop is unfolded in this file.

## Hypotheses

`encode_frame_refines` needs its `len` argument to be the payload length (`send` passes the
value `u32::try_from` returns, so the length fits a `u32`) and room on the output vector for the
frame (Aeneas bounds a `Vec` by `Usize.max` and panics beyond it; a frame adds at most seven bytes
to the payload: marker, up to five length bytes, check byte).

`parse_frame_refines` needs no hypothesis. Its postcondition `ParsePost` is a case split rather
than an equivalence in one place: a frame declaring a length of `2 ^ 32` or more is parsed by the
model (whose varint decoder is over `Nat`) and rejected by the extraction (`Overlong`). The
disjunct is stated, and it is unreachable for any wire the channel wrote, since every frame on it
is `FrameOK`.

`ParsePost` is typed as an Aeneas `WP.Post`, and `parse_frame_refines` is stated with `WP.spec`
directly rather than the `⦃ o => .. ⦄` notation. The two are the same proposition up to eta; the
named post keeps the proof's intermediate goals type-correct at `instances` transparency, which
`simp` needs to reduce the extracted `match`es.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (marker parseFrame encodeFrame lenBytes)

/-- Frame encoder refinement: the extracted `encode_frame` appends exactly the specification's
frame of the payload (marker, varint length, payload, bitwise CRC-8) to the output, and never
fails, given `len` equal to the payload length and room for the frame.
`[EXTRACTED: aeneas + bridge]` -/
theorem encode_frame_refines (payload : Slice Std.U8) (len : Std.U32) (out : alloc.vec.Vec Std.U8)
    (hlen : len.val = payload.val.length)
    (hw : out.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.encode_frame payload len out
      ⦃ v => bitsOf v.val = bitsOf out.val ++ FramedChannel.Channel.encodeFrame (bitsOf payload.val) ⦄ := by
  unfold channel.encode_frame
  step*
  step with FramedChannel.Bridge.varint.encode_refines as ⟨out2, h2⟩
  · simp only [alloc.vec.Vec.length, out1_post, List.length_append, List.length_singleton]; omega
  have hel := FramedChannel.Varint.encode_length_le len.val (by scalar_tac)
  have hl2 : out2.val.length = out.val.length + 1 + (FramedChannel.Varint.encode len.val).length := by
    have := congrArg List.length h2
    simp only [varint.bytesOf, List.length_map, List.length_append, out1_post,
      List.length_singleton] at this
    exact this
  step with FramedChannel.Bridge.vec_extend_from_slice_spec core.clone.CloneU8 (fun _ => rfl) as ⟨out3, h3⟩
  step with FramedChannel.Bridge.crc8.crc8_refines as ⟨c, hc⟩
  step*
  have hb2 : bitsOf out2.val = bitsOf out1.val ++ FramedChannel.Channel.lenBytes payload.val.length := by
    have := congrArg (List.map (BitVec.ofNat 8)) h2
    simp only [← bitsOf_eq_bytesOf_map, List.map_append] at this
    rw [← hlen]
    exact this
  have hlp : (bitsOf payload.val).length = payload.val.length := by simp [bitsOf]
  rw [v_post, h3]
  simp only [bitsOf, List.map_append] at hb2 hc ⊢
  rw [hb2, out1_post]
  simp only [bitsOf] at hlp
  simp only [FramedChannel.Channel.encodeFrame, hlp, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.cons_append, List.nil_append, hc]
  simp [channel.MARKER, FramedChannel.Channel.marker]

/-- The varint bridge's byte abstraction is the CRC bridge's, read as naturals. -/
theorem bytesOf_eq_map_toNat (l : List Std.U8) : varint.bytesOf l = (bitsOf l).map BitVec.toNat := by
  simp [varint.bytesOf, bitsOf, List.map_map]

/-- `split_first` of an empty slice. -/
theorem split_first_nil (wire : Slice Std.U8) (h : wire.val = []) :
    core.slice.Slice.split_first wire = ok none := by
  unfold core.slice.Slice.split_first
  split
  · rfl
  · rename_i x xs h'; rw [h] at h'; cases h'

/-- `split_first` of a non-empty slice. -/
theorem split_first_cons (wire : Slice Std.U8) (x : Std.U8) (xs : List Std.U8) (h : wire.val = x :: xs) :
    ∃ rest : Slice Std.U8, core.slice.Slice.split_first wire = ok (some (x, rest)) ∧ rest.val = xs := by
  unfold core.slice.Slice.split_first
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i y ys h'
    rw [h] at h'
    injection h' with h1 h2
    subst h1 h2
    exact ⟨_, rfl, by simp⟩

/-- `bitsOf` on a cons. -/
theorem bitsOf_cons (x : Std.U8) (xs : List Std.U8) : bitsOf (x :: xs) = x.bv :: bitsOf xs := rfl

/-- The extracted `MARKER` is the specification's `marker`. -/
theorem marker_bv : channel.MARKER.bv = marker := by
  simp [channel.MARKER, marker]

/-- The specification parser rejects a frame not starting with the marker. -/
theorem parseFrame_cons_ne (m : BitVec 8) (rest : List (BitVec 8)) (h : m ≠ marker) :
    parseFrame (m :: rest) = .fail := by
  simp [parseFrame, h]

/-- The specification parser rejects a frame whose length prefix does not decode. -/
theorem parseFrame_marker_fail (rest : List (BitVec 8))
    (h : FramedChannel.Varint.decode (rest.map BitVec.toNat) = .fail) :
    parseFrame (marker :: rest) = .fail := by
  simp [parseFrame, h]

/-- The specification parser after a decoded length prefix that consumed `k` bytes. -/
theorem parseFrame_marker_ok (rest : List (BitVec 8)) (n k : Nat)
    (h : FramedChannel.Varint.decode (rest.map BitVec.toNat) = .ok (n, (rest.map BitVec.toNat).drop k)) :
    parseFrame (marker :: rest) =
      (match (rest.drop k).drop n with
       | c :: tl =>
         if ((rest.drop k).take n).length = n ∧ c = FramedChannel.Crc8.crc8Bits ((rest.drop k).take n) then
           .ok ((rest.drop k).take n, tl)
         else .fail
       | [] => .fail) := by
  simp only [parseFrame, if_true, h, ← List.map_drop, FramedChannel.Channel.ofNat_toNat_map]
  rfl

/-- Frame parser refinement: the extracted `parse_frame` never fails, and its result is related to
the specification's `parseFrame` of the same bytes by `ParsePost`. The varint length and the CRC-8
are reached only through `decode_refines` and `crc8_refines`. `[EXTRACTED: aeneas + bridge]` -/
theorem parse_frame_refines (wire : Slice Std.U8) :
    WP.spec (channel.parse_frame wire) (ParsePost (bitsOf wire.val)) := by
  unfold channel.parse_frame
  rcases (show wire.val = [] ∨ ∃ x xs, wire.val = x :: xs by
      cases wire.val <;> simp) with hw | ⟨first, xs, hw⟩
  · rw [split_first_nil wire hw]
    simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,
      ParsePost, hw, bitsOf, parseFrame]
  · obtain ⟨rest, hsf, hrest⟩ := split_first_cons wire first xs hw
    rw [hsf]
    by_cases hm : first = channel.MARKER
    · subst hm
      simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch]
      obtain ⟨r, hr_eq, hr⟩ := (WP.spec_equiv_exists _ _).mp (varint.decode_refines rest)
      rw [hr_eq]
      simp only [bind_tc_ok]
      rcases r with ⟨n, used⟩ | e
      · simp only [varint.DecPost] at hr
        obtain ⟨hk, hd⟩ := hr
        simp only [varint.bytesOf, List.length_map] at hk
        rw [bytesOf_eq_map_toNat, hrest] at hd
        have hmodel := parseFrame_marker_ok (bitsOf xs) n.val used.val (by rw [hd])
        have hn1 : (UScalar.cast UScalarTy.Usize n).val = n.val := by
          simp only [UScalar.cast_val_eq]
          apply Nat.mod_eq_of_lt
          have h1 : n.val < 2 ^ 32 := n.hBounds
          have h2 : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
            apply Nat.pow_le_pow_right (by omega)
            rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
          omega
        simp only [lift, bind_tc_ok]
        simp
        obtain ⟨o1, ho1, ho1p⟩ := (WP.spec_equiv_exists _ _).mp
          (FramedChannel.Bridge.slice_get_range_from_spec rest { start := used })
        rw [ho1]
        rw [if_pos hk] at ho1p
        subst ho1p
        simp
        have hL : List.drop used.val (bitsOf xs) = bitsOf (rest.drop used).val := by
          simp [bitsOf, ← hrest, List.map_drop]
        rw [hL] at hmodel
        rw [hw, bitsOf_cons, marker_bv]
        obtain ⟨o2, ho2, ho2p⟩ := (WP.spec_equiv_exists _ _).mp
          (FramedChannel.Bridge.slice_get_range_to_spec (rest.drop used) { «end» := UScalar.cast UScalarTy.Usize n })
        rw [ho2]
        simp only [hn1] at ho2p
        by_cases hlen : n.val ≤ (rest.drop used).val.length
        · obtain ⟨s', rfl, hs'⟩ := ho2p.1 hlen
          simp
          obtain ⟨payload, hp, hpp⟩ := (WP.spec_equiv_exists _ _).mp
            (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s' (fun _ _ => rfl))
          rw [hp]
          simp only [bind_tc_ok]
          obtain ⟨o3, ho3, ho3p⟩ := (WP.spec_equiv_exists _ _).mp
            (FramedChannel.Bridge.slice_get_usize_spec (rest.drop used) (UScalar.cast UScalarTy.Usize n))
          rw [ho3]
          simp only [bind_tc_ok]
          rw [hn1] at ho3p
          have hpv : payload.val = List.take n.val (rest.drop used).val := by
            rw [← hs', hpp]; rfl
          by_cases hlt : n.val < (rest.drop used).val.length
          · rw [List.getElem?_eq_getElem hlt] at ho3p
            subst ho3p
            simp only
            obtain ⟨c, hc, hcp⟩ := (WP.spec_equiv_exists _ _).mp
              (FramedChannel.Bridge.crc8.crc8_refines (alloc.vec.Vec.deref payload))
            rw [hc]
            simp only [bind_tc_ok]
            have hdrop : List.drop n.val (bitsOf (rest.drop used).val) =
                ((rest.drop used).val[n.val]'hlt).bv :: List.drop (n.val + 1) (bitsOf (rest.drop used).val) := by
              simp only [bitsOf]
              rw [← List.map_drop, List.drop_eq_getElem_cons hlt]
              simp [List.map_drop]
            have htake : List.take n.val (bitsOf (rest.drop used).val) = bitsOf payload.val := by
              simp [bitsOf, hpv, List.map_take]
            rw [hdrop, htake] at hmodel
            have hderef : (alloc.vec.Vec.deref payload).val = payload.val := by
              simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
            rw [hderef] at hcp
            have hplen : (bitsOf payload.val).length = n.val := by
              simp only [bitsOf, List.length_map, hpv, List.length_take]; omega
            have hwl : wire.val.length ≤ Usize.max := wire.property
            have hrl : (rest.drop used).val.length = rest.val.length - used.val := by
              simp [Slice.drop]
            have hwr : wire.val.length = rest.val.length + 1 := by rw [hw, ← hrest]; simp
            by_cases hbc : ((rest.drop used).val[n.val]'hlt).val = c.val
            · simp only [hbc, if_true]
              obtain ⟨i1, hi1, hi1p⟩ := (WP.spec_equiv_exists _ _).mp
                (UScalar.add_spec (x := 1#usize) (y := used) (by scalar_tac))
              rw [hi1]
              simp only [bind_tc_ok]
              obtain ⟨i2, hi2, hi2p⟩ := (WP.spec_equiv_exists _ _).mp
                (UScalar.add_spec (x := i1) (y := UScalar.cast UScalarTy.Usize n) (by scalar_tac))
              rw [hi2]
              simp only [bind_tc_ok]
              obtain ⟨i3, hi3, hi3p⟩ := (WP.spec_equiv_exists _ _).mp
                (UScalar.add_spec (x := i2) (y := 1#usize) (by scalar_tac))
              rw [hi3]
              simp only [bind_tc_ok, WP.spec_ok, ParsePost]
              have hi3v : i3.val = used.val + n.val + 2 := by scalar_tac
              refine ⟨?_, ?_⟩
              · simp only [List.length_cons, bitsOf, List.length_map]; rw [← hrest]; omega
              · rw [hmodel]
                have hb : ((rest.drop used).val[n.val]'hlt).bv = FramedChannel.Crc8.crc8Bits (bitsOf payload.val) := by
                  have hbe : (rest.drop used).val[n.val]'hlt = c := UScalar.eq_of_val_eq hbc
                  rw [hbe, hcp]
                simp only [hplen, hb, and_self, if_true]
                congr 2
                rw [hi3v, show used.val + n.val + 2 = (used.val + (n.val + 1)) + 1 by omega,
                  List.drop_succ_cons, ← hL, List.drop_drop]
            · simp only [hbc, if_false, WP.spec_ok, ParsePost]
              left
              rw [hmodel]
              simp only [hplen, true_and]
              rw [if_neg]
              intro h
              apply hbc
              have := h.trans hcp.symm
              exact congrArg UScalar.val ((UScalar.eq_equiv_bv_eq _ _).mpr this)
          · have hnone : (rest.drop used).val[n.val]? = none := by
              apply List.getElem?_eq_none; omega
            rw [hnone] at ho3p
            subst ho3p
            simp only [bind_tc_ok, WP.spec_ok, ParsePost,
              core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
            left
            rw [hmodel]
            have : List.drop n.val (bitsOf (rest.drop used).val) = [] := by
              simp only [bitsOf]
              apply List.drop_eq_nil_of_le
              simp only [List.length_map]; omega
            rw [this]
        · have := ho2p.2 (by omega)
          subst this
          simp only [bind_tc_ok, WP.spec_ok, ParsePost,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
          left
          rw [hmodel]
          have : List.drop n.val (bitsOf (rest.drop used).val) = [] := by
            simp only [bitsOf] at *
            apply List.drop_eq_nil_of_le
            simp only [List.length_map]; omega
          rw [this]
      · simp only [WP.spec_ok, ParsePost]
        rw [hw, bitsOf_cons, marker_bv]
        simp only [varint.DecPost] at hr
        rw [bytesOf_eq_map_toNat, hrest] at hr
        rcases hr with hf | ⟨n, rem, hd, hn⟩
        · exact Or.inl (parseFrame_marker_fail _ hf)
        · exact Or.inr ⟨_, n, rem, rfl, hd, hn⟩
    · have hne : (first != channel.MARKER) = true := by simpa using hm
      have hmv : ¬ first.val = channel.MARKER.val := fun h => hm (UScalar.eq_of_val_eq h)
      simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch, hmv, ParsePost]
      rw [hw, bitsOf_cons]
      left
      apply parseFrame_cons_ne
      intro h; apply hm
      rw [← marker_bv] at h
      rw [UScalar.eq_equiv_bv_eq]
      exact h

/-- `drop_front` drops exactly `n` bytes (all of them when `n` exceeds the length), and never
fails. -/
theorem drop_front_refines (b : Slice Std.U8) (n : Std.Usize) :
    channel.drop_front b n ⦃ v => bitsOf v.val = (bitsOf b.val).drop n.val ⦄ := by
  unfold channel.drop_front
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
    have : v.val = (b.drop n).val := by rw [hv]; rfl
    simp [this, bitsOf, List.map_drop]
  · rw [if_neg hn] at hop
    subst hop
    simp only [WP.spec_ok]
    simp only [bitsOf]
    rw [List.drop_eq_nil_of_le (by simp only [List.length_map]; omega)]
    simp

/-- The length prefix of an encoded frame decodes to the payload length, whatever follows. -/
theorem decode_encodeFrame_tail (p rest : List (BitVec 8)) (hp : p.length < 2 ^ 32) :
    FramedChannel.Varint.decode ((lenBytes p.length ++ (p ++ [FramedChannel.Crc8.crc8Bits p]) ++ rest).map BitVec.toNat) =
      .ok (p.length, (p ++ [FramedChannel.Crc8.crc8Bits p] ++ rest).map BitVec.toNat) := by
  have hv := FramedChannel.Varint.varint_roundtrip p.length hp
  have hd := FramedChannel.Channel.decodeF_append 5 1 0 p.length (FramedChannel.Varint.encode p.length)
    ((p ++ [FramedChannel.Crc8.crc8Bits p] ++ rest).map BitVec.toNat) hv
  simp only [List.map_append, FramedChannel.Channel.toNat_lenBytes, List.append_assoc] at hd ⊢
  exact hd

/-- The extracted frame round trip: on any wire that starts with the specification's encoding of a
payload `p` whose length fits a `u32`, the extracted parser returns exactly `p` and consumes exactly
the frame. The only hypothesis is the length bound (`send` refuses longer payloads). The
declared-length divergence of `ParsePost` cannot arise, because the declared length is `p.length`.
`[EXTRACTED: aeneas + bridge]` -/
theorem parse_frame_encode_frame_extracted (w : Slice Std.U8) (p rest : List (BitVec 8))
    (hp : p.length ≤ U32.max) (hw : bitsOf w.val = FramedChannel.Channel.encodeFrame p ++ rest) :
    channel.parse_frame w
      ⦃ o => ∃ v used, o = some (v, used) ∧ bitsOf v.val = p ∧
        used.val = (FramedChannel.Channel.encodeFrame p).length ⦄ := by
  have hp' : p.length < 2 ^ 32 := by scalar_tac
  have hpf := FramedChannel.Channel.parseFrame_encodeFrame p rest hp'
  apply WP.spec_mono (parse_frame_refines w)
  intro o ho
  rcases o with _ | ⟨v, used⟩
  · simp only [ParsePost] at ho
    rcases ho with hf | ⟨rest', n, rem, hw', hd, hn⟩
    · rw [hw, hpf] at hf; cases hf
    · rw [hw] at hw'
      simp only [encodeFrame, List.cons_append, List.cons.injEq] at hw'
      obtain ⟨-, hr⟩ := hw'
      rw [← hr, decode_encodeFrame_tail p rest hp'] at hd
      simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hd
      omega
  · simp only [ParsePost] at ho
    obtain ⟨hle, hpar⟩ := ho
    rw [hw] at hpar hle
    rw [hpf] at hpar
    simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hpar
    obtain ⟨h1, h2⟩ := hpar
    refine ⟨v, used, rfl, h1.symm, ?_⟩
    have := congrArg List.length h2
    simp only [List.length_drop, List.length_append] at this hle
    omega

/-- A 126-byte payload's frame starts with two marker bytes: its one length byte is `0x7E`. -/
theorem encodeFrame_take2_len126 (p : List (BitVec 8)) (hp : p.length = 126) :
    (encodeFrame p).take 2 = [marker, marker] := by
  simp [encodeFrame, hp, lenBytes, FramedChannel.Varint.encode, FramedChannel.Varint.encodeF, marker]

/-- A 126-byte payload's frame is 129 bytes long. -/
theorem encodeFrame_length_len126 (p : List (BitVec 8)) (hp : p.length = 126) :
    (encodeFrame p).length = 129 := by
  simp [encodeFrame, hp, lenBytes, FramedChannel.Varint.encode, FramedChannel.Varint.encodeF]

/-- The marker-byte frame, at the extracted parser: a payload of exactly 126 bytes has `0x7E` (the
frame marker) as its single varint length byte, so its frame starts with two marker bytes. The
extracted `parse_frame` still returns exactly that payload and consumes all 129 bytes: it reads the
second marker as a length, not as a frame boundary. `[EXTRACTED: aeneas + bridge]` -/
theorem parse_frame_len126_extracted (w : Slice Std.U8) (p rest : List (BitVec 8))
    (hp : p.length = 126) (hw : bitsOf w.val = FramedChannel.Channel.encodeFrame p ++ rest) :
    (FramedChannel.Channel.encodeFrame p).take 2 =
        [FramedChannel.Channel.marker, FramedChannel.Channel.marker] ∧
      channel.parse_frame w
        ⦃ o => ∃ v used, o = some (v, used) ∧ bitsOf v.val = p ∧ used.val = 129 ⦄ := by
  refine ⟨encodeFrame_take2_len126 p hp, ?_⟩
  apply WP.spec_mono (parse_frame_encode_frame_extracted w p rest (by scalar_tac) hw)
  rintro o ⟨v, used, ho, hv, hu⟩
  exact ⟨v, used, ho, hv, by rw [hu, encodeFrame_length_len126 p hp]⟩

end FramedChannel.Bridge.channel

#print axioms FramedChannel.Bridge.channel.encode_frame_refines
#print axioms FramedChannel.Bridge.channel.bytesOf_eq_map_toNat
#print axioms FramedChannel.Bridge.channel.split_first_nil
#print axioms FramedChannel.Bridge.channel.split_first_cons
#print axioms FramedChannel.Bridge.channel.bitsOf_cons
#print axioms FramedChannel.Bridge.channel.marker_bv
#print axioms FramedChannel.Bridge.channel.parseFrame_cons_ne
#print axioms FramedChannel.Bridge.channel.parseFrame_marker_fail
#print axioms FramedChannel.Bridge.channel.parseFrame_marker_ok
#print axioms FramedChannel.Bridge.channel.parse_frame_refines
#print axioms FramedChannel.Bridge.channel.drop_front_refines
#print axioms FramedChannel.Bridge.channel.decode_encodeFrame_tail
#print axioms FramedChannel.Bridge.channel.parse_frame_encode_frame_extracted
#print axioms FramedChannel.Bridge.channel.encodeFrame_take2_len126
#print axioms FramedChannel.Bridge.channel.encodeFrame_length_len126
#print axioms FramedChannel.Bridge.channel.parse_frame_len126_extracted
