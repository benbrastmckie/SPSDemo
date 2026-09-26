-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Varint.Instance
import FramedChannelAeneas.Bridge.Zigzag.Mapping

/-!
# Bridge/Zigzag/Instance: the extracted signed codec, its public theorems and `CodecLaws`

`[EXTRACTED: aeneas + bridge]` -- the signed codec row, stated about the Rust as extracted.

## Distilled at the bridge, not re-derived

This is the point of the unit, in the bridge half as well as the model half. `encode_refines` and
`roundtrip_extracted` are each one scalar step (`zigzag_spec`, from `Mapping.lean`) followed by
`WP.spec_mono` of the **varint bridge's own theorem** at the mapped value -- no LEB128 loop
reasoning is repeated here, and no loop lemma appears in this file at all. The three decode
theorems are the same shape over `varint.decode_ok_refines`, `decode_complete` and
`decode_err_iff`.

## Error agreement is immediate

`zigzag.decode_i32` forwards the `VarintError` its `varint.decode_u32` call returns, unchanged, so
this unit introduces no error taxonomy of its own and `decode_err_iff` is the varint's own error
characterisation transported across the value mapping. That is exactly what the model's
`decode_fail_iff` says on its side.

## The interface instance

`instCodecLaws_extracted` is `CodecLaws` at `ExtractedZigzagI32` over `Std.I32`, discharged from
`roundtrip_extracted`, `encode_refines` and the model's `encode_length_le`. `Dom` is `True`: the
`i32` range is carried by the type. `sliceOfBytes_bytesOf` and `bytesOf_lt` are reused unchanged
from the varint bridge.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.zigzag
open framed_channel

/-! ## Encode: one scalar step, then the varint's own refinement -/

/-- The extracted `encode_i32` appends exactly the bytes the model's `encode` computes. One
`zigzag_spec` step, then `varint.encode_refines` at the mapped value. `[EXTRACTED: aeneas +
bridge]` -/
theorem encode_refines (n : Std.I32) (out : alloc.vec.Vec Std.U8)
    (h : out.length + 5 ≤ Usize.max) :
    zigzag.encode_i32 n out
      ⦃ v => varint.bytesOf v.val
          = varint.bytesOf out.val ++ FramedChannel.Zigzag.encode n.val ⦄ := by
  unfold zigzag.encode_i32
  step with zigzag_spec as ⟨i, hi⟩
  apply WP.spec_mono (FramedChannel.Bridge.varint.encode_refines i out h)
  intro v hv
  rw [hv, FramedChannel.Zigzag.encode_eq, hi]

/-! ## Decode: three corollaries of the varint's own decode theorems

Each is `step with` the varint bridge's own decode spec, then a case split on the extracted
result and one `unzigzag_spec` step on the success branch. No decode loop is unfolded here.
-/

/-- The signed decode, spelled through the varint model's decode. Definitional; the bridge
rewrites with it, as `FramedChannel.Zigzag.encode_eq` is rewritten with on the encode side. -/
theorem decode_eq (bs : List Nat) :
    FramedChannel.Zigzag.decode bs =
      match FramedChannel.Varint.decode bs with
      | .ok (m, rest) => .ok (FramedChannel.Zigzag.unzigzag m, rest)
      | .fail => .fail := rfl

/-- Success agreement: an extracted `Ok((v, k))` is a model success with the same signed value and
the same residual bytes. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_ok_refines (s : Slice Std.U8) :
    zigzag.decode_i32 s ⦃ r => ∀ v k, r = .Ok (v, k) →
      FramedChannel.Zigzag.decode (varint.bytesOf s.val)
        = .ok (v.val, (varint.bytesOf s.val).drop k.val) ⦄ := by
  unfold zigzag.decode_i32
  step with FramedChannel.Bridge.varint.decode_ok_refines s as ⟨r, hr⟩
  rcases r with ⟨m, k⟩ | e
  · have hm := hr m k rfl
    step with unzigzag_spec as ⟨w, hw⟩
    rintro v k' hvk
    cases hvk
    rw [decode_eq, hm, hw]
  · simp only [WP.spec_ok]
    rintro v k' hvk
    exact absurd hvk (by simp)

/-- Completeness: a model success inside the codec's declared domain is an extracted `Ok` with the
same signed value, a consumed count within the input, and the same residual bytes. The domain
hypothesis is the model instance's own `Dom`, and it is needed for the same reason the varint's
`decode_complete` needs `n < 2 ^ 32`: the model decodes over an unbounded `Nat`, while the Rust
rejects an over-wide fifth group. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_complete (s : Slice Std.U8) (n : Int) (rest : List Nat)
    (h : FramedChannel.Zigzag.decode (varint.bytesOf s.val) = .ok (n, rest))
    (hdom : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) :
    zigzag.decode_i32 s ⦃ r => ∃ v k, r = .Ok (v, k) ∧ v.val = n ∧ k.val ≤ s.val.length ∧
      (varint.bytesOf s.val).drop k.val = rest ⦄ := by
  rw [decode_eq] at h
  match hd : FramedChannel.Varint.decode (varint.bytesOf s.val) with
  | .fail => rw [hd] at h; exact absurd h (by simp)
  | .ok (m, r0) =>
    rw [hd] at h
    simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hn, hr0⟩ := h
    -- `n` is `unzigzag m`, so `zigzag n = m` by the bijection, and `zigzag_lt` bounds it.
    have hmz : FramedChannel.Zigzag.zigzag n = m := by
      rw [← hn]; exact FramedChannel.Zigzag.zigzag_unzigzag m
    have hlt : m < 2 ^ 32 := hmz ▸ FramedChannel.Zigzag.zigzag_lt n hdom
    unfold zigzag.decode_i32
    step with FramedChannel.Bridge.varint.decode_complete s m r0 hd hlt
      as ⟨v, k, res, hrv, hv, hk, hdrop⟩
    rw [hrv]
    step with unzigzag_spec as ⟨w, hw⟩
    exact ⟨w, k, rfl, by rw [hw, hv, hn], hk, by rw [hdrop, hr0]⟩

/-- Error agreement: the extracted signed decode returns `Err` exactly when the underlying varint
decode does -- which is exactly the varint bridge's own characterisation, transported across the
value mapping. `decode_i32` forwards the `VarintError` unchanged, so this unit introduces no error
taxonomy of its own. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_err_iff (s : Slice Std.U8) :
    zigzag.decode_i32 s ⦃ r => (∃ e, r = .Err e) ↔
      (FramedChannel.Varint.decode (varint.bytesOf s.val) = .fail ∨
        ∃ n rest, FramedChannel.Varint.decode (varint.bytesOf s.val) = .ok (n, rest)
          ∧ 2 ^ 32 ≤ n) ⦄ := by
  unfold zigzag.decode_i32
  step with FramedChannel.Bridge.varint.decode_err_iff s as ⟨r, hr⟩
  rcases r with ⟨m, k⟩ | e
  · step with unzigzag_spec as ⟨w, hw⟩
    constructor
    · rintro ⟨e, he⟩; exact absurd he (by simp)
    · intro hc
      exact absurd (hr.mpr hc) (by simp)
  · simp only [WP.spec_ok]
    exact ⟨fun _ => hr.mp ⟨e, rfl⟩, fun _ => ⟨e, rfl⟩⟩

/-! ## The extracted round trip: varint's own round trip, plus one scalar step -/

/-- The extracted round trip, for every machine `i32`: decoding what `encode_i32` wrote returns the
value with every byte consumed. No bound hypothesis -- the `i32` range is the type's.
`[EXTRACTED: aeneas + bridge]` -/
theorem roundtrip_extracted (n : Std.I32) :
    zigzag.encode_i32 n (alloc.vec.Vec.new Std.U8) ⦃ v =>
      zigzag.decode_i32 (alloc.vec.Vec.deref v) ⦃ r => r = .Ok (n, alloc.vec.Vec.len v) ⦄ ⦄ := by
  unfold zigzag.encode_i32
  step with zigzag_spec as ⟨i, hi⟩
  apply WP.spec_mono (FramedChannel.Bridge.varint.roundtrip_extracted i)
  intro v hv
  unfold zigzag.decode_i32
  step with hv as ⟨r, hr⟩
  subst hr
  simp only []
  step with unzigzag_spec as ⟨w, hw⟩
  have hwn : w = n := by
    apply IScalar.eq_of_val_eq
    rw [hw, hi, FramedChannel.Zigzag.unzigzag_zigzag]
  simp [hwn]

/-! ## The interface instance on the extracted signed codec -/

/-- The codec laws on the extracted signed codec, at every machine `i32`.
`[EXTRACTED: aeneas + bridge]` -/
theorem instCodecLaws_extracted : CodecLaws ExtractedZigzagI32 Std.I32 where
  round_trip a _ := by
    obtain ⟨v, hv, hdec⟩ := (WP.spec_equiv_exists _ _).mp (roundtrip_extracted a)
    obtain ⟨v', hv', hbytes⟩ := (WP.spec_equiv_exists _ _).mp
      (encode_refines a (alloc.vec.Vec.new Std.U8) (by simp; scalar_tac))
    rw [hv] at hv'
    obtain rfl := Result.ok_injective hv'
    obtain ⟨r, hr, rfl⟩ := (WP.spec_equiv_exists _ _).mp hdec
    have henc : CodecModel.encode (C := ExtractedZigzagI32) a = varint.bytesOf v.val := by
      show extEncode a = _
      simp only [extEncode, hv, Result.match.ok]
    have hlen : (varint.bytesOf v.val).length ≤ Usize.max := by
      simp only [varint.bytesOf, List.length_map]
      exact v.slice.property
    show extDecode (CodecModel.encode (C := ExtractedZigzagI32) a) = _
    rw [henc]
    unfold extDecode
    rw [dif_pos ⟨hlen, FramedChannel.Bridge.varint.bytesOf_lt v.val⟩,
      FramedChannel.Bridge.varint.sliceOfBytes_bytesOf v hlen, hr]
    simp only [Result.match.ok]
    simp [varint.bytesOf]
  length_le a _ := by
    obtain ⟨v, hv, hbytes⟩ := (WP.spec_equiv_exists _ _).mp
      (encode_refines a (alloc.vec.Vec.new Std.U8) (by simp; scalar_tac))
    show (extEncode a).length ≤ 5
    simp only [extEncode, hv, Result.match.ok, hbytes]
    simp only [varint.bytesOf, alloc.vec.Vec.new]
    exact FramedChannel.Zigzag.encode_length_le a.val ⟨a.hmin, a.hmax⟩

end FramedChannel.Bridge.zigzag

#print axioms FramedChannel.Bridge.zigzag.encode_refines
#print axioms FramedChannel.Bridge.zigzag.decode_eq
#print axioms FramedChannel.Bridge.zigzag.decode_ok_refines
#print axioms FramedChannel.Bridge.zigzag.decode_complete
#print axioms FramedChannel.Bridge.zigzag.decode_err_iff
#print axioms FramedChannel.Bridge.zigzag.roundtrip_extracted
#print axioms FramedChannel.Bridge.zigzag.instCodecLaws_extracted
