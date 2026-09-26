-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Model.Varint.Theorems
import FramedChannel.Model.Zigzag.Defs

/-!
# Model/Zigzag/Theorems: the zigzag signed varint

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/zigzag.rs` (`zigzag`,
`unzigzag`, `encode_i32`, `decode_i32`), giving the codec interface its second value type: `Leb128`
sits at the naturals, `Stuff` at byte lists, and `ZigzagI32` here at `Int`.

## Distilled, not re-derived

`zigzag_roundtrip` and `encode_length_le` are recorded on the `retrieval` rung: they are *retrieved*
from `CodecLaws.round_trip` and `CodecLaws.length_le` at `C := Varint.Leb128` -- the LEB128 codec's
own laws, reached through the L1 class rather than through its raw theorems -- plus the one new
arithmetic fact `zigzag_lt`. Nothing about LEB128 is re-proved here, and that is the point of the
unit: it is the Distillation row of `../../README.md`'s relations table exercised across two units.
The spelling in `Defs.lean` is what makes the rung honest; see that module's docstring.

The bijection (`unzigzag_zigzag`, `zigzag_unzigzag`) is registered *hypothesis-free*. `zigzag` is a
total bijection `Int → Nat` at this model, which is strictly stronger than mutual inversion on the
`i32` range; the range hypothesis appears only in `zigzag_lt`, where it is genuinely needed, and
hence in the instance's `Dom`. `Evidence/Countermodels.lean` refutes `zigzag_lt` without that
hypothesis, at exactly `2 ^ 31`.
-/

namespace FramedChannel.Zigzag

/-! ## The bound that enters the varint's domain -/

/-- On the `i32` range, the zigzag image lies in the varint's claimed `u32` domain. This is the one
new arithmetic fact the unit needs, and the hypothesis is not decoration: `zigzag_lt_unbounded` in
`Evidence/Countermodels.lean` refutes the unconditional form at `2 ^ 31`, the first value outside
`i32`. The converse holds too -- `Dom n ↔ zigzag n < 2 ^ 32` -- so the instance's `Dom` is the exact
preimage of the varint's domain rather than a conservative guess. `[PROVED: kernel]` -/
theorem zigzag_lt (n : Int) (h : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) : zigzag n < 2 ^ 32 := by
  rung grind => grind [zigzag]

/-! ## The bijection, hypothesis-free -/

/-- `unzigzag` inverts `zigzag` on all of `Int`, with no range hypothesis. `[PROVED: kernel]` -/
theorem unzigzag_zigzag (n : Int) : unzigzag (zigzag n) = n := by
  rung grind => grind [zigzag, unzigzag]

/-- `zigzag` inverts `unzigzag` on all of `Nat`, with no range hypothesis. Together with
`unzigzag_zigzag` this makes `zigzag` a bijection `Int ≃ Nat`. `[PROVED: kernel]` -/
theorem zigzag_unzigzag (m : Nat) : zigzag (unzigzag m) = m := by
  rung grind => grind [zigzag, unzigzag]

/-! ## Error agreement -/

/-- Error agreement: this codec fails exactly when the underlying LEB128 codec fails. The model has
a single `.fail` and carries no error taxonomy of its own, matching `decode_i32`, which forwards
`VarintError` unchanged. `[PROVED: kernel]` -/
theorem decode_fail_iff (bs : List Nat) :
    decode bs = .fail ↔ CodecModel.decode (C := Varint.Leb128) (α := Nat) bs = .fail := by
  rung grind => grind [decode]

/-! ## The two laws, retrieved from `CodecLaws` at `Leb128` -/

/-- The round-trip law, retrieved: `CodecLaws.round_trip` at `Leb128` applied to `zigzag n` (legal
by `zigzag_lt`), then `unzigzag_zigzag`. No LEB128 reasoning appears. `[PROVED: kernel]` -/
theorem zigzag_roundtrip (n : Int) (h : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) :
    decode (encode n) = .ok (n, []) := by
  rung retrieval =>
    simp only [decode, encode,
      CodecLaws.round_trip (C := Varint.Leb128) (zigzag n) (zigzag_lt n h), unzigzag_zigzag]

/-- The five-byte bound, retrieved: it *is* the varint's own `CodecLaws.length_le`, at `zigzag n`.
`[PROVED: kernel]` -/
theorem encode_length_le (n : Int) (h : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) : (encode n).length ≤ 5 := by
  rung retrieval => exact CodecLaws.length_le (C := Varint.Leb128) (zigzag n) (zigzag_lt n h)

/-! ## The interface instance

`CodecModel` (L0) and `CodecLaws` (L1) are specification, declared in `Spec/Codec.lean`. This is the
interface's second value type. -/

/-- The refinement certificate as an interface instance, at `α = Int`. `[PROVED: kernel]` -/
instance instCodecLaws : CodecLaws ZigzagI32 Int where
  round_trip := zigzag_roundtrip
  length_le := encode_length_le

ladder_record% instCodecLaws instance

/-! ## Supporting lemma

Unregistered, for the bridge: the projection spelling of `encode` is definitionally the direct one,
so `Bridge/Zigzag/Instance.lean` can rewrite between them. -/

/-- The projection spelling and the direct spelling of `encode` agree by `rfl`. -/
theorem encode_eq (n : Int) : encode n = Varint.encode (zigzag n) := rfl

#print axioms zigzag_lt
#print axioms unzigzag_zigzag
#print axioms zigzag_unzigzag
#print axioms decode_fail_iff
#print axioms zigzag_roundtrip
#print axioms encode_length_le
#print axioms instCodecLaws
#print axioms encode_eq

end FramedChannel.Zigzag
