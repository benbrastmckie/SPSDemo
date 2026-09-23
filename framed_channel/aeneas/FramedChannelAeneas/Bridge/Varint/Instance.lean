-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Varint.Decode

/-!
# Bridge/Varint/Instance: the extracted LEB128 codec, its public theorems and `CodecLaws`

`[EXTRACTED: aeneas + bridge]` -- the codec row, stated about the Rust as extracted.

## The decode theorems

Each is a corollary of `decode_refines` (`Decode.lean` beside this file), and each is a total
triple, so it also says the extracted `decode_u32` returns (never panics) on every slice:

* `decode_ok_refines` (success agreement): an extracted `Ok((v, k))` is a model success with the
  same value, leaving `bytes[k..]`;
* `decode_complete` (completeness): a model success with a value below `2^32` is an extracted
  `Ok` with that value, consuming exactly the bytes the model consumed;
* `decode_err_iff` (error agreement): the extracted decode returns `Err` exactly when the model
  fails or returns a value at or above `2^32`. The second disjunct is the Rust's stricter
  `Overlong` rejection of an over-wide fifth group; it is the true relation, not a weakening.

## The extracted round trip, with no hypothesis

`roundtrip_extracted n` decodes what `encode_u32 n` wrote into an empty vector and gets `n` back
with every byte consumed, for every `n : Std.U32`. The `u32` bound is `n.hBounds`, carried by the
machine integer: no `n < 2^32` hypothesis appears. It chains `encode_refines`, the model's
`varint_roundtrip` and `decode_complete`.

## The interface instance

`instCodecModelExtracted` is `CodecModel` at the tag `ExtractedLeb128` over `Std.U32`: `encode`
runs the extracted `encode_u32` on an empty vector, and `decode` runs the extracted `decode_u32`
on the slice holding the input. `Dom` is the whole type. A byte list no Rust byte slice can hold
(longer than `usize::MAX`, or containing a value of 256 or more) is refused; neither law reaches
such an input, because every encoding is a list of machine bytes. `instCodecLaws_extracted` is
discharged from `roundtrip_extracted`, `encode_refines` and the model's `encode_length_le`.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.varint
open framed_channel

/-- Success agreement: an extracted `Ok((v, k))` is a model success with the same value and the
same residual bytes. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_ok_refines (s : Slice Std.U8) :
    varint.decode_u32 s ⦃ r => ∀ v k, r = .Ok (v, k) →
      FramedChannel.Varint.decode (bytesOf s.val) = .ok (v.val, (bytesOf s.val).drop k.val) ⦄ := by
  apply WP.spec_mono (decode_refines s)
  rintro r hr v k rfl
  exact hr.2

/-- Completeness: a model success below `2^32` is an extracted `Ok` with the same value, a
consumed count within the input, and the same residual bytes. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_complete (s : Slice Std.U8) (n : Nat) (rest : List Nat)
    (h : FramedChannel.Varint.decode (bytesOf s.val) = .ok (n, rest)) (hn : n < 2 ^ 32) :
    varint.decode_u32 s ⦃ r => ∃ v k, r = .Ok (v, k) ∧ v.val = n ∧ k.val ≤ s.val.length ∧
      (bytesOf s.val).drop k.val = rest ⦄ := by
  apply WP.spec_mono (decode_refines s)
  intro r hr
  match r, hr with
  | .Ok (v, k), ⟨hk, hd⟩ =>
    rw [h] at hd
    simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨hv, hr⟩ := hd
    refine ⟨v, k, rfl, hv.symm, by simpa [bytesOf] using hk, hr.symm⟩
  | .Err _, hd =>
    rcases hd with hd | ⟨n', rest', hd, hge⟩
    · rw [h] at hd; exact absurd hd (by simp)
    · rw [h] at hd
      simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hd
      omega

/-- Error agreement: the extracted decode returns `Err` exactly when the model fails or returns a
value at or above `2^32`. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_err_iff (s : Slice Std.U8) :
    varint.decode_u32 s ⦃ r => (∃ e, r = .Err e) ↔
      (FramedChannel.Varint.decode (bytesOf s.val) = .fail ∨
        ∃ n rest, FramedChannel.Varint.decode (bytesOf s.val) = .ok (n, rest) ∧ 2 ^ 32 ≤ n) ⦄ := by
  apply WP.spec_mono (decode_refines s)
  intro r hr
  match r, hr with
  | .Ok (v, k), ⟨_, hd⟩ =>
    constructor
    · rintro ⟨e, he⟩; cases he
    · rintro (hf | ⟨n, rest, hn, hge⟩)
      · rw [hd] at hf; exact absurd hf (by simp)
      · rw [hd] at hn
        simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hn
        have : v.val < 2 ^ 32 := v.hBounds
        omega
  | .Err e, hd => exact ⟨fun _ => hd, fun _ => ⟨e, rfl⟩⟩

/-- The extracted round trip, for every machine `u32`: decoding what `encode_u32` wrote returns
the value with every byte consumed. No bound hypothesis. `[EXTRACTED: aeneas + bridge]` -/
theorem roundtrip_extracted (n : Std.U32) :
    varint.encode_u32 n (alloc.vec.Vec.new Std.U8) ⦃ v =>
      varint.decode_u32 (alloc.vec.Vec.deref v) ⦃ r => r = .Ok (n, alloc.vec.Vec.len v) ⦄ ⦄ := by
  apply WP.spec_mono (encode_refines n (alloc.vec.Vec.new Std.U8) (by simp; scalar_tac))
  intro v hv
  have hs : bytesOf (alloc.vec.Vec.deref v).val = FramedChannel.Varint.encode n.val := by
    simpa [alloc.vec.Vec.deref, bytesOf] using hv
  apply WP.spec_mono (decode_complete _ n.val []
    (by rw [hs]; exact FramedChannel.Varint.varint_roundtrip n.val n.hBounds) n.hBounds)
  rintro r ⟨w, k, rfl, hw, hk, hdrop⟩
  have hkl : k.val = v.val.length := by
    simp only [List.drop_eq_nil_iff, bytesOf, List.length_map] at hdrop
    simp [alloc.vec.Vec.deref] at hk hdrop
    omega
  have hw' : w = n := UScalar.eq_of_val_eq hw
  have hk' : k = alloc.vec.Vec.len v := UScalar.eq_of_val_eq (by simp [hkl])
  rw [hw', hk']

/-! ## The interface instance on the extracted codec -/

/-- Every abstracted machine byte is below 256. -/
theorem bytesOf_lt (l : List Std.U8) : ∀ b ∈ bytesOf l, b < 256 := by
  intro b hb
  simp only [bytesOf, List.mem_map] at hb
  obtain ⟨x, -, rfl⟩ := hb
  exact x.hBounds

/-- Re-slicing the abstraction of a vector gives back the vector's own slice. -/
theorem sliceOfBytes_bytesOf (v : alloc.vec.Vec Std.U8) (h : (bytesOf v.val).length ≤ Usize.max) :
    sliceOfBytes (bytesOf v.val) h = alloc.vec.Vec.deref v := by
  apply Slice.ext
  simp only [sliceOfBytes, alloc.vec.Vec.deref, bytesOf, Slice.from_val, List.map_map]
  refine (List.map_congr_left (fun x _ => ?_)).trans (List.map_id _)
  apply UScalar.eq_of_val_eq
  simp only [Function.comp_apply, id_eq, UScalar.ofNatCore_val_eq]
  exact Nat.mod_eq_of_lt x.hBounds

/-- The codec laws on the extracted codec, at every `u32`. `[EXTRACTED: aeneas + bridge]` -/
theorem instCodecLaws_extracted : CodecLaws ExtractedLeb128 Std.U32 where
  round_trip a _ := by
    obtain ⟨v, hv, hdec⟩ := (WP.spec_equiv_exists _ _).mp (roundtrip_extracted a)
    obtain ⟨v', hv', hbytes⟩ := (WP.spec_equiv_exists _ _).mp
      (encode_refines a (alloc.vec.Vec.new Std.U8) (by simp; scalar_tac))
    rw [hv] at hv'
    obtain rfl := Result.ok_injective hv'
    obtain ⟨r, hr, rfl⟩ := (WP.spec_equiv_exists _ _).mp hdec
    have henc : CodecModel.encode (C := ExtractedLeb128) a = bytesOf v.val := by
      show extEncode a = _
      simp only [extEncode, hv, Result.match.ok]
    have hlen : (bytesOf v.val).length ≤ Usize.max := by
      simp only [bytesOf, List.length_map]
      exact v.slice.property
    show extDecode (CodecModel.encode (C := ExtractedLeb128) a) = _
    rw [henc]
    unfold extDecode
    rw [dif_pos ⟨hlen, bytesOf_lt v.val⟩, sliceOfBytes_bytesOf v hlen, hr]
    simp only [Result.match.ok]
    simp [bytesOf]
  length_le a _ := by
    obtain ⟨v, hv, hbytes⟩ := (WP.spec_equiv_exists _ _).mp
      (encode_refines a (alloc.vec.Vec.new Std.U8) (by simp; scalar_tac))
    show (extEncode a).length ≤ 5
    simp only [extEncode, hv, Result.match.ok, hbytes]
    simp only [bytesOf, alloc.vec.Vec.new]
    exact FramedChannel.Varint.encode_length_le a.val a.hBounds

end FramedChannel.Bridge.varint

#print axioms FramedChannel.Bridge.varint.decode_ok_refines
#print axioms FramedChannel.Bridge.varint.decode_complete
#print axioms FramedChannel.Bridge.varint.decode_err_iff
#print axioms FramedChannel.Bridge.varint.roundtrip_extracted
#print axioms FramedChannel.Bridge.varint.bytesOf_lt
#print axioms FramedChannel.Bridge.varint.sliceOfBytes_bytesOf
#print axioms FramedChannel.Bridge.varint.instCodecLaws_extracted
