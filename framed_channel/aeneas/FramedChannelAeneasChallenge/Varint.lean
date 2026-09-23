-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Varint.Defs

/-!
# FramedChannelAeneasChallenge.Varint: approved statements (extracted LEB128 codec)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/Varint/{Encode,Decode,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.varint
open framed_channel

/-- Encode refinement: the extracted `encode_u32` appends exactly the model's LEB128 encoding of
`n`, and never fails, given room for five more bytes. -/
theorem encode_refines (n : Std.U32) (out : alloc.vec.Vec Std.U8)
    (h : out.length + 5 ≤ Usize.max) :
    varint.encode_u32 n out
      ⦃ v => bytesOf v.val = bytesOf out.val ++ FramedChannel.Varint.encode n.val ⦄ := sorry
end FramedChannel.Bridge.varint

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.varint
open framed_channel
end FramedChannel.Bridge.varint

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.varint
open framed_channel

/-- Success agreement: an extracted `Ok((v, k))` is a model success with the same value and the
same residual bytes. -/
theorem decode_ok_refines (s : Slice Std.U8) :
    varint.decode_u32 s ⦃ r => ∀ v k, r = .Ok (v, k) →
      FramedChannel.Varint.decode (bytesOf s.val) = .ok (v.val, (bytesOf s.val).drop k.val) ⦄ := sorry

/-- Completeness: a model success below `2^32` is an extracted `Ok` with the same value, a
consumed count within the input, and the same residual bytes. -/
theorem decode_complete (s : Slice Std.U8) (n : Nat) (rest : List Nat)
    (h : FramedChannel.Varint.decode (bytesOf s.val) = .ok (n, rest)) (hn : n < 2 ^ 32) :
    varint.decode_u32 s ⦃ r => ∃ v k, r = .Ok (v, k) ∧ v.val = n ∧ k.val ≤ s.val.length ∧
      (bytesOf s.val).drop k.val = rest ⦄ := sorry

/-- Error agreement: the extracted decode returns `Err` exactly when the model fails or returns a
value at or above `2^32`. -/
theorem decode_err_iff (s : Slice Std.U8) :
    varint.decode_u32 s ⦃ r => (∃ e, r = .Err e) ↔
      (FramedChannel.Varint.decode (bytesOf s.val) = .fail ∨
        ∃ n rest, FramedChannel.Varint.decode (bytesOf s.val) = .ok (n, rest) ∧ 2 ^ 32 ≤ n) ⦄ := sorry

/-- The extracted round trip, for every machine `u32`: decoding what `encode_u32` wrote returns
the value with every byte consumed. No bound hypothesis. -/
theorem roundtrip_extracted (n : Std.U32) :
    varint.encode_u32 n (alloc.vec.Vec.new Std.U8) ⦃ v =>
      varint.decode_u32 (alloc.vec.Vec.deref v) ⦃ r => r = .Ok (n, alloc.vec.Vec.len v) ⦄ ⦄ := sorry

/-- The codec laws on the extracted codec, at every `u32`. -/
theorem instCodecLaws_extracted : CodecLaws ExtractedLeb128 Std.U32 := sorry
end FramedChannel.Bridge.varint
