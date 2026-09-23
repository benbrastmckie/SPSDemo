-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Crc8.Defs

/-!
# FramedChannelAeneasChallenge.Crc8: approved statements (extracted CRC-8 checksum)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/Crc8/{Bitwise,Table,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.crc8
open framed_channel
open FramedChannel.Crc8 (shift1)

/-- Bitwise refinement: the extracted `crc8` never fails, and computes the model's bitwise CRC of
the slice's bytes. -/
theorem crc8_refines (s : Slice Std.U8) :
    crc8.crc8 s ⦃ c => c.bv = FramedChannel.Crc8.crc8Bits (bitsOf s.val) ⦄ := sorry
end FramedChannel.Bridge.crc8

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.crc8
open framed_channel
section KernelDecide

/-- Table agreement: the extracted `TABLE` is the model's table, entry for entry. -/
theorem table_agrees : crc8.TABLE.val.map (·.bv) = FramedChannel.Crc8.table.toList := sorry
end KernelDecide

/-- Table refinement: the extracted `crc8_table` never fails, and computes the model's table CRC
of the slice's bytes. -/
theorem crc8_table_refines (s : Slice Std.U8) :
    crc8.crc8_table s ⦃ c => c.bv = FramedChannel.Crc8.crc8Table (bitsOf s.val) ⦄ := sorry
end FramedChannel.Bridge.crc8

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.crc8
open framed_channel

/-- The table/bitwise equivalence at the extracted level: on every slice the two extracted
functions return the same byte. -/
theorem crc8_table_eq_extracted (s : Slice Std.U8) :
    crc8.crc8_table s ⦃ t => crc8.crc8 s ⦃ b => t = b ⦄ ⦄ := sorry

/-- The checksum laws on the extracted bitwise CRC-8. -/
theorem instChecksumLaws_extractedBitwise : ChecksumLaws ExtractedBitwise := sorry

/-- The checksum laws on the extracted table-driven CRC-8. -/
theorem instChecksumLaws_extractedTabled : ChecksumLaws ExtractedTabled := sorry
end FramedChannel.Bridge.crc8
