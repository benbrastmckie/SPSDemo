-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Model.Varint.Defs

/-!
# FramedChannelChallenge.Varint: approved statements (LEB128 codec model)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Model/Varint/Theorems.lean`. See `lean/FramedChannelChallenge.lean` for what a Challenge
module is and what the gate checks.
-/

namespace FramedChannel.Varint

/-- The round-trip law, general form: every `u32` value decodes to itself with nothing left
over. -/
theorem varint_roundtrip (n : Nat) (h : n < 2 ^ 32) : decode (encode n) = .ok (n, []) := sorry

/-- Bounds: on the domain the codec claims (`u32`), the encoding is never longer than five bytes
-- the counterpart of `encode_u32`'s five-iteration loop and of `assert!(bytes.len() <= 5)` in
`rust/tests/differential.rs`.

The `n < 2 ^ 32` hypothesis is not decoration: `encodeF 5` emits a sixth byte once `n >= 128 ^ 5`,
so the unconditional form of this statement is false. The bound is a property of the claimed
domain. -/
theorem encode_length_le (n : Nat) (h : n < 2 ^ 32) : (encode n).length ≤ 5 := sorry

/-- The refinement certificate as an interface instance: the LEB128 codec satisfies the codec
laws, discharged from `varint_roundtrip` and `encode_length_le`. -/
instance instCodecLaws : CodecLaws Leb128 Nat := sorry
end FramedChannel.Varint
