-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Crc8.Bitwise
import FramedChannelAeneas.Bridge.Crc8.Table

/-!
# Bridge/Crc8/Instance: table/bitwise equivalence and `ChecksumLaws` on the extracted CRC-8

`[EXTRACTED: aeneas + bridge]` -- the checksum rows, stated about the Rust as
extracted.

## The equivalence at the extracted level

`crc8_table_eq_extracted`: on every slice, the extracted `crc8_table` and the extracted `crc8`
return the same byte. It is kernel-only, obtained from the two refinements (`Table.lean`,
`Bitwise.lean`) and the model's `crc8_table_eq_bits`. No new SAT-backed step: the model's flagged
`crc8_step_linear` row and its kernel replay `crc8_step_linear_kernel` are untouched, and neither
is used here.

## Two instances of one interface, on the extracted functions

`ExtractedBitwise` and `ExtractedTabled` are component tags with `ChecksumModel` instances whose
operations are the extracted code, lowered through `Result.match`:

* `step`: the extracted inner loop run on `crc ^ b` (bitwise), or the lookup into the extracted
  `TABLE` (table);
* `seed`: `0`;
* `digest`: the extracted `crc8` / `crc8_table` on the slice holding the bytes, whenever
  `bs.length <= usize::MAX`.

**The digest fallback.** `ChecksumModel.digest` is total over `List (BitVec 8)`, but an Aeneas
`Slice` holds at most `Usize.max` elements, and `digest_snoc` must hold across that boundary. So a
list longer than any Rust slice digests by the model fold instead. On every list a Rust slice can
hold, the digest *is* the extracted function. The primary refinement claims, `crc8_refines` and
`crc8_table_refines`, quantify over every `Slice` and have no fallback.

The laws are derived, not re-proved: `digest_eq` / `step_eq` identify each lowered operation with
the model's, and the model instances' `digest_snoc` finishes.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.crc8
open framed_channel

/-- The table/bitwise equivalence at the extracted level: on every slice the two extracted
functions return the same byte. `[EXTRACTED: aeneas + bridge]` -/
theorem crc8_table_eq_extracted (s : Slice Std.U8) :
    crc8.crc8_table s ⦃ t => crc8.crc8 s ⦃ b => t = b ⦄ ⦄ := by
  apply WP.spec_mono (crc8_table_refines s)
  intro t ht
  apply WP.spec_mono (crc8_refines s)
  intro b hb
  rw [UScalar.eq_equiv_bv_eq]
  exact ht.trans ((FramedChannel.Crc8.crc8_table_eq_bits _).trans hb.symm)

theorem bitsOf_bitsToSlice (bs : List (BitVec 8)) (h : bs.length ≤ Usize.max) :
    bitsOf (bitsToSlice bs h).val = bs := by
  simp [bitsToSlice, bitsOf, List.map_map]

/-- The lowered extracted bitwise step is the model's `stepBits`. -/
theorem extStepBits_eq (c b : BitVec 8) : extStepBits c b = FramedChannel.Crc8.stepBits c b := by
  obtain ⟨r, hr, hrv⟩ := (WP.spec_equiv_exists _ _).mp (inner_refines (⟨c ^^^ b⟩ : Std.U8))
  simp only [extStepBits, hr, Result.match.ok]
  exact hrv

/-- The extracted table lookup is the model's `stepTable`. -/
theorem extStepTable_eq (c b : BitVec 8) : extStepTable c b = FramedChannel.Crc8.stepTable c b := by
  have hlt : (c ^^^ b).toNat < crc8.TABLE.val.length := by
    rw [table_length]; exact (c ^^^ b).isLt
  obtain ⟨v, hv⟩ : ∃ v, crc8.TABLE.val[(c ^^^ b).toNat]? = some v :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  simp only [extStepTable, hv]
  exact table_entry_bv ⟨c⟩ ⟨b⟩ v hv

/-- The lowered extracted bitwise digest is the model's `crc8Bits`, on every list. -/
theorem extDigestBits_eq (bs : List (BitVec 8)) :
    extDigestBits bs = FramedChannel.Crc8.crc8Bits bs := by
  unfold extDigestBits
  split
  · rename_i h
    obtain ⟨r, hr, hrv⟩ := (WP.spec_equiv_exists _ _).mp (crc8_refines (bitsToSlice bs h))
    simp only [hr, Result.match.ok]
    rw [hrv, bitsOf_bitsToSlice]
  · rfl

/-- The lowered extracted table digest is the model's `crc8Table`, on every list. -/
theorem extDigestTable_eq (bs : List (BitVec 8)) :
    extDigestTable bs = FramedChannel.Crc8.crc8Table bs := by
  unfold extDigestTable
  split
  · rename_i h
    obtain ⟨r, hr, hrv⟩ := (WP.spec_equiv_exists _ _).mp (crc8_table_refines (bitsToSlice bs h))
    simp only [hr, Result.match.ok]
    rw [hrv, bitsOf_bitsToSlice]
  · rfl

/-- The checksum laws on the extracted bitwise CRC-8. `[EXTRACTED: aeneas + bridge]` -/
theorem instChecksumLaws_extractedBitwise : ChecksumLaws ExtractedBitwise where
  digest_nil := by
    show extDigestBits [] = 0
    rw [extDigestBits_eq]
    rfl
  digest_snoc bs b := by
    show extDigestBits (bs ++ [b]) = extStepBits (extDigestBits bs) b
    rw [extDigestBits_eq, extDigestBits_eq, extStepBits_eq]
    exact FramedChannel.Crc8.instChecksumLawsBitwise.digest_snoc bs b

/-- The checksum laws on the extracted table-driven CRC-8. `[EXTRACTED: aeneas + bridge]` -/
theorem instChecksumLaws_extractedTabled : ChecksumLaws ExtractedTabled where
  digest_nil := by
    show extDigestTable [] = 0
    rw [extDigestTable_eq]
    rfl
  digest_snoc bs b := by
    show extDigestTable (bs ++ [b]) = extStepTable (extDigestTable bs) b
    rw [extDigestTable_eq, extDigestTable_eq, extStepTable_eq]
    exact FramedChannel.Crc8.instChecksumLawsTabled.digest_snoc bs b

end FramedChannel.Bridge.crc8

#print axioms FramedChannel.Bridge.crc8.crc8_table_eq_extracted
#print axioms FramedChannel.Bridge.crc8.bitsOf_bitsToSlice
#print axioms FramedChannel.Bridge.crc8.extStepBits_eq
#print axioms FramedChannel.Bridge.crc8.extStepTable_eq
#print axioms FramedChannel.Bridge.crc8.extDigestBits_eq
#print axioms FramedChannel.Bridge.crc8.extDigestTable_eq
#print axioms FramedChannel.Bridge.crc8.instChecksumLaws_extractedBitwise
#print axioms FramedChannel.Bridge.crc8.instChecksumLaws_extractedTabled
