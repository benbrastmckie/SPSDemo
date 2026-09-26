-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Model.Zigzag.Defs

/-!
# FramedChannelChallenge.Zigzag: approved statements (zigzag signed-varint codec model)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Model/Zigzag/Theorems.lean`. See `lean/FramedChannelChallenge.lean` for what a
Challenge module is and what the gate checks.
-/

namespace FramedChannel.Zigzag

/-- The bound that enters the varint's domain: on the `i32` range the zigzag image lies inside the
`u32` domain the LEB128 codec claims. The hypothesis is not decoration -- `zigzag_lt_unbounded` in
`lean/FramedChannel/Evidence/Countermodels.lean` refutes the unconditional form at `2 ^ 31`. -/
theorem zigzag_lt (n : Int) (h : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) : zigzag n < 2 ^ 32 := sorry

/-- One direction of the bijection, hypothesis-free: `unzigzag` inverts `zigzag` on all of `Int`,
which is strictly stronger than mutual inversion on the `i32` range. -/
theorem unzigzag_zigzag (n : Int) : unzigzag (zigzag n) = n := sorry

/-- The other direction, hypothesis-free: `zigzag` inverts `unzigzag` on all of `Nat`. -/
theorem zigzag_unzigzag (m : Nat) : zigzag (unzigzag m) = m := sorry

/-- Error agreement: the signed codec fails exactly when the underlying LEB128 codec fails. The
model carries a single `.fail` and no taxonomy of its own, matching `decode_i32`, which forwards
`VarintError` unchanged. -/
theorem decode_fail_iff (bs : List Nat) :
    decode bs = .fail ↔ CodecModel.decode (C := Varint.Leb128) (α := Nat) bs = .fail := sorry

/-- The round-trip law on the `i32` range, retrieved from `CodecLaws.round_trip` at `Leb128` rather
than re-derived: no LEB128 reasoning appears in the proof. -/
theorem zigzag_roundtrip (n : Int) (h : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) :
    decode (encode n) = .ok (n, []) := sorry

/-- The five-byte bound, retrieved: it *is* the varint's own `CodecLaws.length_le`, at `zigzag n`. -/
theorem encode_length_le (n : Int) (h : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) : (encode n).length ≤ 5 := sorry

/-- The refinement certificate as an interface instance, at the interface's second value type
`α = Int`, discharged from `zigzag_roundtrip` and `encode_length_le`. -/
instance instCodecLaws : CodecLaws ZigzagI32 Int := sorry

end FramedChannel.Zigzag
