-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Model.Varint.Defs

/-!
# Model/Varint/Theorems: LEB128 encoder and decoder

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/varint.rs` (`encode_u32`,
`decode_u32`), over the specification layer's `Result` (`Spec/Result.lean`). Bytes are modeled
as `Nat` values below 256; the Rust `u32` bound appears as the hypothesis `n < 2 ^ 32` on the
round-trip theorem rather than as a bounded integer type.

## Termination by fuel

Both Rust loops are bounded to five iterations, and both Lean functions are structurally recursive
on an explicit fuel argument, `5` for each. The termination measure is the fuel, and the theorems
state what the function does *within* that fuel, never that a fuel-exhausted call agrees with
anything: `encodeF 0 n` emits the low seven bits and stops, `decodeF 0 ...` fails. Neither branch
is reachable from `encode`/`decode` below `2 ^ 32`, and `varint_roundtrip` states the round trip
for every such `n`.

`varint_roundtrip` is this component's E2 registry row; it and `encode_length_le` are closed by
`grind` over the four definitions (proof ladder, `Ladder.lean`).
-/

namespace FramedChannel.Varint

/-- Every emitted byte is below 256: `n % 128 + 128 < 256`, and the final byte is below 128. -/
theorem encodeF_bytes_lt (fuel n : Nat) : ∀ b ∈ encodeF fuel n, b < 256 := by
  induction fuel generalizing n with
  | zero =>
    intro b hb
    simp only [encodeF, List.mem_singleton] at hb
    subst hb
    omega
  | succ f ih =>
    intro b hb
    simp only [encodeF] at hb
    split at hb
    · simp only [List.mem_singleton] at hb
      omega
    · simp only [List.mem_cons] at hb
      rcases hb with hb | hb
      · omega
      · exact ih _ b hb

/-- The round-trip law: every `u32` value decodes to itself with nothing left over.
`[PROVED: kernel]` -/
theorem varint_roundtrip (n : Nat) (h : n < 2 ^ 32) : decode (encode n) = .ok (n, []) := by
  rung grind => grind [decode, encode, decodeF, encodeF]

/-! ## Bounds: the encoding never exceeds five bytes on the claimed domain -/

/-- Bounds: on the domain the codec claims (`u32`), the encoding is never longer than five bytes
-- the counterpart of `encode_u32`'s five-iteration loop and of `assert!(bytes.len() <= 5)` in
`rust/tests/differential.rs`.

The `n < 2 ^ 32` hypothesis is not decoration: `encodeF 5` emits a sixth byte once `n >= 128 ^ 5`,
so the unconditional form of this statement is false. The bound is a property of the claimed
domain. `[PROVED: kernel]` -/
theorem encode_length_le (n : Nat) (h : n < 2 ^ 32) : (encode n).length ≤ 5 := by
  rung grind =>
    simp only [encode, encodeF] at *
    grind

/-! ## The interface instance

`CodecModel` (L0) and `CodecLaws` (L1) are specification, declared in `Spec/Codec.lean`.
`Leb128` is the component tag the stateless codec is indexed by. -/

/-- The refinement certificate as an interface instance: the LEB128 codec satisfies the codec
laws, discharged from `varint_roundtrip` and `encode_length_le`. `[PROVED: kernel]` -/
instance instCodecLaws : CodecLaws Leb128 Nat where
  round_trip := varint_roundtrip
  length_le := encode_length_le

ladder_record% instCodecLaws instance

#print axioms encodeF_bytes_lt
#print axioms varint_roundtrip
#print axioms encode_length_le
#print axioms instCodecLaws

end FramedChannel.Varint
