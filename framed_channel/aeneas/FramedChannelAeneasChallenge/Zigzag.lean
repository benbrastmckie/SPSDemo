-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Zigzag.Defs

/-!
# FramedChannelAeneasChallenge.Zigzag: approved statements (extracted zigzag signed varint)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/Zigzag/{Mapping,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.zigzag
open framed_channel

/-- The extracted `zigzag`'s signed shift and xor computes the model's arithmetic zigzag map, on
every machine `i32`. -/
theorem zigzag_spec (n : Std.I32) :
    zigzag.zigzag n ⦃ v => v.val = FramedChannel.Zigzag.zigzag n.val ⦄ := sorry

/-- The extracted `unzigzag` is the model's `unzigzag`, on every machine `u32`. -/
theorem unzigzag_spec (m : Std.U32) :
    zigzag.unzigzag m ⦃ v => v.val = FramedChannel.Zigzag.unzigzag m.val ⦄ := sorry

/-- Encode refinement: the extracted `encode_i32` appends exactly the model's zigzag LEB128
encoding of `n`, and never fails, given room for five more bytes. -/
theorem encode_refines (n : Std.I32) (out : alloc.vec.Vec Std.U8)
    (h : out.length + 5 ≤ Usize.max) :
    zigzag.encode_i32 n out
      ⦃ v => varint.bytesOf v.val
          = varint.bytesOf out.val ++ FramedChannel.Zigzag.encode n.val ⦄ := sorry

/-- Success agreement: an extracted `Ok((v, k))` is a model success with the same signed value and
the same residual bytes. -/
theorem decode_ok_refines (s : Slice Std.U8) :
    zigzag.decode_i32 s ⦃ r => ∀ v k, r = .Ok (v, k) →
      FramedChannel.Zigzag.decode (varint.bytesOf s.val)
        = .ok (v.val, (varint.bytesOf s.val).drop k.val) ⦄ := sorry

/-- Completeness: a model success inside the codec's declared domain is an extracted `Ok` with the
same signed value, a consumed count within the input, and the same residual bytes. -/
theorem decode_complete (s : Slice Std.U8) (n : Int) (rest : List Nat)
    (h : FramedChannel.Zigzag.decode (varint.bytesOf s.val) = .ok (n, rest))
    (hdom : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) :
    zigzag.decode_i32 s ⦃ r => ∃ v k, r = .Ok (v, k) ∧ v.val = n ∧ k.val ≤ s.val.length ∧
      (varint.bytesOf s.val).drop k.val = rest ⦄ := sorry

/-- Error agreement: the extracted signed decode returns `Err` exactly when the underlying varint
decode does. `decode_i32` forwards the `VarintError` unchanged, so no new taxonomy appears. -/
theorem decode_err_iff (s : Slice Std.U8) :
    zigzag.decode_i32 s ⦃ r => (∃ e, r = .Err e) ↔
      (FramedChannel.Varint.decode (varint.bytesOf s.val) = .fail ∨
        ∃ n rest, FramedChannel.Varint.decode (varint.bytesOf s.val) = .ok (n, rest)
          ∧ 2 ^ 32 ≤ n) ⦄ := sorry

/-- The extracted round trip, for every machine `i32`: decoding what `encode_i32` wrote returns the
value with every byte consumed. No bound hypothesis -- the `i32` range is the type's. -/
theorem roundtrip_extracted (n : Std.I32) :
    zigzag.encode_i32 n (alloc.vec.Vec.new Std.U8) ⦃ v =>
      zigzag.decode_i32 (alloc.vec.Vec.deref v) ⦃ r => r = .Ok (n, alloc.vec.Vec.len v) ⦄ ⦄ := sorry

/-- The codec laws on the extracted signed codec, at every machine `i32`. -/
theorem instCodecLaws_extracted : CodecLaws ExtractedZigzagI32 Std.I32 := sorry
end FramedChannel.Bridge.zigzag
