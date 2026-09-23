-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import Std.Tactic.BVDecide
import FramedChannel.Model.Crc8.Defs

/-!
# Model/Crc8/Theorems: the checksum component

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/crc8.rs`. Polynomial `0x07`,
initial value `0`, no reflection, no final xor (the "CRC-8" of the check-value tables:
`crc8 "123456789" = 0xF4`). Bytes are `BitVec 8`; no Mathlib is needed, `BitVec` is core.

## The three theorems and their routes

* `crc8_step_linear`: the per-byte step is GF(2)-linear, closed by `bv_decide` (a SAT call through
  the bundled CaDiCaL). Its `#print axioms` therefore shows a native `bv_decide` helper axiom, so it
  is tagged `[PROVED: compiler-trusting]` -- the example's one instance of that row,
  registered unverified and carried as `check.sh`'s only flagged allowance.
* `crc8_step_linear_kernel`: the same statement replayed in the kernel from `shift1_xor` (one
  polynomial iteration is xor-linear) and `round_xor` (so are eight). `[PROVED: kernel]`. It sits
  *beside* the `bv_decide` row, not in place of it, which stays counted as unverified.
* `crc8_table_eq_bits`: the table lookup and the bitwise loop compute the same checksum on every
  input. The per-entry lemma `table_entry` (256 cases) is closed by kernel `decide`; the list
  lemma is an induction. `[PROVED: kernel]`.

## Rust to Lean mapping

| Rust `crc8.rs`                | Lean                       |
|-------------------------------|----------------------------|
| `POLY: u8 = 0x07`             | `poly : BitVec 8`          |
| inner `for _ in 0..8` loop    | `shift1`, unrolled 8 times |
| `crc8(bytes)`                 | `crc8Bits`                 |
| `TABLE: [u8; 256]`            | `table`                    |
| `crc8_table(bytes)`           | `crc8Table`                |
-/

namespace FramedChannel.Crc8

/-- GF(2)-linearity of the byte step. `[PROVED: compiler-trusting]` (`bv_decide`); its kernel
replay is `crc8_step_linear_kernel` below. -/
theorem crc8_step_linear (a b : BitVec 8) :
    stepBits (a ^^^ b) 0 = stepBits a 0 ^^^ stepBits b 0 := by
  rung bv_decide =>
    simp only [stepBits, round, shift1, poly]
    bv_decide

/-- One polynomial iteration is xor-linear. `[PROVED: kernel]` -/
theorem shift1_xor (a b : BitVec 8) : shift1 (a ^^^ b) = shift1 a ^^^ shift1 b := by
  unfold shift1
  rw [BitVec.msb_xor]
  cases ha : a.msb <;> cases hb : b.msb <;> simp only [Bool.xor_false, Bool.xor_true,
    Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true, BitVec.shiftLeft_xor_distrib]
  · ac_rfl
  · ac_rfl
  · rw [show a <<< 1 ^^^ poly ^^^ (b <<< 1 ^^^ poly) =
        a <<< 1 ^^^ b <<< 1 ^^^ (poly ^^^ poly) by ac_rfl,
      BitVec.xor_self, BitVec.xor_zero]

/-- The eight iterations are xor-linear. `[PROVED: kernel]` -/
theorem round_xor (a b : BitVec 8) : round (a ^^^ b) = round a ^^^ round b := by
  simp only [round, shift1_xor]

/-- Kernel replay of `crc8_step_linear`, with no `bv_decide` and no compiler-trusting axiom.
`[PROVED: kernel]` -/
theorem crc8_step_linear_kernel (a b : BitVec 8) :
    stepBits (a ^^^ b) 0 = stepBits a 0 ^^^ stepBits b 0 := by
  -- The row exists to avoid `bv_decide`, so that rung is excluded from its audit, and the record
  -- says so.
  rung manual (excluding bv_decide) =>
    -- `simp only [BitVec.xor_zero]` does not fire on the literal `0`; a local lemma does.
    have hz : ∀ x : BitVec 8, x ^^^ 0 = x := fun x => BitVec.xor_zero
    simp only [stepBits, hz]
    exact round_xor a b

/-! ## The table and the bitwise loop agree

`table_entry` decides 256 cases in the kernel and the declarations below unfold it, so the whole
group runs under one raised recursion depth. -/

section KernelDecide
set_option maxRecDepth 100000

/-- Every table entry is the eight-iteration round on its index (256 cases, kernel `decide`).
`[PROVED: kernel]` -/
theorem table_entry : ∀ i : Fin 256, table.getD i.val 0 = round (BitVec.ofNat 8 i.val) := by
  decide +kernel

theorem stepTable_eq_stepBits (crc b : BitVec 8) : stepTable crc b = stepBits crc b := by
  have h := table_entry ⟨(crc ^^^ b).toNat, (crc ^^^ b).isLt⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

theorem foldl_stepTable_eq (bs : List (BitVec 8)) :
    ∀ acc, bs.foldl stepTable acc = bs.foldl stepBits acc := by
  induction bs with
  | nil => intro acc; simp only [List.foldl]
  | cons b bs ih =>
    intro acc
    simp only [List.foldl, stepTable_eq_stepBits]
    exact ih _

/-- The table implementation agrees with the bitwise loop on every input. `[PROVED: kernel]` -/
theorem crc8_table_eq_bits (bs : List (BitVec 8)) : crc8Table bs = crc8Bits bs := by
  rung retrieval => exact foldl_stepTable_eq bs 0

/-- The standard check value. -/
example : crc8Bits [0x31#8, 0x32#8, 0x33#8, 0x34#8, 0x35#8, 0x36#8, 0x37#8, 0x38#8, 0x39#8]
    = 0xf4#8 := by decide +kernel

/-! ### Failure-freedom: the table index is always in range -/

/-- The table has exactly 256 entries. `[PROVED: kernel]` -/
theorem table_size : table.size = 256 := by rfl

/-- Failure-freedom: the index `stepTable` computes is always inside the table, so the `getD`
default is unreachable -- the Lean counterpart of "no out-of-bounds index in the Rust". The `0`
fallback in `crc8_table`'s `TABLE.get(..)` is, by this theorem, dead code. `[PROVED: kernel]` -/
theorem stepTable_index_in_range (crc b : BitVec 8) : (crc ^^^ b).toNat < table.size := by
  rung manual =>
    rw [table_size]
    exact (crc ^^^ b).isLt

end KernelDecide

/-! ## The interface instances

`ChecksumModel` (L0) and `ChecksumLaws` (L1) are specification, declared in `Spec/Checksum.lean`.
There are **two** canonical models here, not one. That is the equivalence row in interface terms:
`table CRC-8 ≃ bitwise CRC-8` is two instances of one interface whose digests agree on every
input (`crc8_table_eq_bits`). -/

/-- The refinement certificate as an interface instance: the bitwise loop satisfies the checksum
laws. `[PROVED: kernel]` -/
instance instChecksumLawsBitwise : ChecksumLaws Bitwise where
  digest_nil := rfl
  digest_snoc bs b := by
    show crc8Bits (bs ++ [b]) = stepBits (crc8Bits bs) b
    simp only [crc8Bits, List.foldl_append, List.foldl_cons, List.foldl_nil]

ladder_record% instChecksumLawsBitwise instance

/-- The same laws at the table implementation, discharged from the bitwise instance through
`crc8_table_eq_bits` and `stepTable_eq_stepBits` -- no reproof of the fold. This pair of instances
is the equivalence row: one interface, two models, agreeing digests. Both are registered, so that
the two core `ChecksumLaws` instances are registered exactly as the bridge's two extracted ones
are (`Registry.lean`'s coverage note records why the earlier double-counting argument was
dropped). `[PROVED: kernel]` -/
instance instChecksumLawsTabled : ChecksumLaws Tabled where
  digest_nil := rfl
  digest_snoc bs b := by
    show crc8Table (bs ++ [b]) = stepTable (crc8Table bs) b
    rw [crc8_table_eq_bits, crc8_table_eq_bits, stepTable_eq_stepBits]
    simp only [crc8Bits, List.foldl_append, List.foldl_cons, List.foldl_nil]

ladder_record% instChecksumLawsTabled instance

#print axioms crc8_step_linear
#print axioms shift1_xor
#print axioms round_xor
#print axioms crc8_step_linear_kernel
#print axioms table_entry
#print axioms crc8_table_eq_bits
#print axioms table_size
#print axioms stepTable_index_in_range
#print axioms instChecksumLawsBitwise
#print axioms instChecksumLawsTabled

end FramedChannel.Crc8
