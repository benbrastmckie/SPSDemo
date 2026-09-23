-- SPDX-License-Identifier: Apache-2.0
/-!
# Spec/Checksum: the checksum interface, `ChecksumModel` (L0) and `ChecksumLaws` (L1)

The same two-layer anatomy `Spec/Queue.lean` gives the queue, at the checksum: operations and
types in `ChecksumModel`, laws over the digest of a byte list in `ChecksumLaws`.

`Model/Crc8/Theorems.lean` gives **two** canonical instances, the bitwise loop and the table lookup. That is
the equivalence row in interface terms: one interface, two models whose digests agree on every
input (`Crc8.crc8_table_eq_bits`).
-/

namespace FramedChannel

/-- L0: the operations of a byte-list checksum, indexed by a component tag `C`. Operations and
types only. -/
class ChecksumModel (C : Type) where
  /-- The per-byte step. -/
  step : BitVec 8 → BitVec 8 → BitVec 8
  /-- The initial value. -/
  seed : BitVec 8
  /-- The digest of a byte list: the abstract observation the laws are stated over. -/
  digest : List (BitVec 8) → BitVec 8

/-- L1: the laws a checksum must satisfy, stated through `digest`. -/
class ChecksumLaws (C : Type) [ChecksumModel C] : Prop where
  /-- The fold law: the empty list digests to the seed. -/
  digest_nil : ChecksumModel.digest (C := C) [] = ChecksumModel.seed (C := C)
  /-- The step law: appending one byte applies exactly one step to the digest so far. -/
  digest_snoc : ∀ (bs : List (BitVec 8)) (b : BitVec 8),
    ChecksumModel.digest (C := C) (bs ++ [b]) =
      ChecksumModel.step (C := C) (ChecksumModel.digest (C := C) bs) b

end FramedChannel
