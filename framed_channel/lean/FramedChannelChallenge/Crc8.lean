-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Model.Crc8.Defs

/-!
# FramedChannelChallenge.Crc8: approved statements (CRC-8 checksum model)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Model/Crc8/Theorems.lean`. See `lean/FramedChannelChallenge.lean` for what a Challenge
module is and what the gate checks.
-/

namespace FramedChannel.Crc8

/-- GF(2)-linearity of the byte step, by `bv_decide`; its kernel
replay is `crc8_step_linear_kernel` below. -/
theorem crc8_step_linear (a b : BitVec 8) :
    stepBits (a ^^^ b) 0 = stepBits a 0 ^^^ stepBits b 0 := sorry

/-- Kernel replay of `crc8_step_linear`, with no `bv_decide` and no compiler-trusting axiom. -/
theorem crc8_step_linear_kernel (a b : BitVec 8) :
    stepBits (a ^^^ b) 0 = stepBits a 0 ^^^ stepBits b 0 := sorry
section KernelDecide

/-- The table implementation agrees with the bitwise loop on every input. -/
theorem crc8_table_eq_bits (bs : List (BitVec 8)) : crc8Table bs = crc8Bits bs := sorry

/-- Failure-freedom: the index `stepTable` computes is always inside the table, so the `getD`
default is unreachable -- the Lean counterpart of "no out-of-bounds index in the Rust". The `0`
fallback in `crc8_table`'s `TABLE.get(..)` is, by this theorem, dead code. -/
theorem stepTable_index_in_range (crc b : BitVec 8) : (crc ^^^ b).toNat < table.size := sorry
end KernelDecide

/-- The refinement certificate as an interface instance: the bitwise loop satisfies the checksum
laws. -/
instance instChecksumLawsBitwise : ChecksumLaws Bitwise := sorry

/-- The same laws at the table implementation: one interface, two models, agreeing digests. -/
instance instChecksumLawsTabled : ChecksumLaws Tabled := sorry
end FramedChannel.Crc8
