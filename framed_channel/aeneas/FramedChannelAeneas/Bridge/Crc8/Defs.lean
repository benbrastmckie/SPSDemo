-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs
import FramedChannel.Model.Crc8.Defs

/-!
# Bridge/Crc8/Defs: extracted bytes, read as the model's bit-vector list

`[HAND-WRITTEN]` -- the abstraction function the CRC-8 refinement theorems (`Bitwise.lean`,
`Table.lean` and `Instance.lean` beside this file) are stated over.

The extracted `crc8.crc8` and `crc8.crc8_table` read a `Slice Std.U8` and return a `Std.U8`. The
hand-written model `FramedChannel.Crc8` (`lean/FramedChannel/Model/Crc8/Theorems.lean`) folds over
`List (BitVec 8)`. A `Std.U8` carries its bit vector as `.bv`, so `bitsOf` maps each machine byte
to it, and a digest is compared through `.bv` as well.

It also defines the extracted checksum's two `ChecksumModel` instances and what they are built
from: `bitsToSlice`, the tags `ExtractedBitwise` and `ExtractedTabled`, and the lowered steps and
digests (`Instance.lean`'s docstring explains the digest fallback beyond `Usize.max`). Every
definition a registered CRC-8 bridge statement mentions is here, so the Challenge module can import
them without importing a registered theorem.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.crc8

/-- The abstraction function: each machine byte to its bit vector. -/
def bitsOf (v : List Std.U8) : List (BitVec 8) := v.map (·.bv)

end FramedChannel.Bridge.crc8

namespace FramedChannel.Bridge.crc8
open framed_channel

/-- A list of bit-vector bytes as a machine slice. -/
def bitsToSlice (bs : List (BitVec 8)) (h : bs.length ≤ Usize.max) : Slice Std.U8 :=
  Slice.from (bs.map fun b => (⟨b⟩ : Std.U8)) (by simpa using h)

/-- The component tag naming the extracted bitwise CRC-8. -/
structure ExtractedBitwise where

/-- The component tag naming the extracted table-driven CRC-8. -/
structure ExtractedTabled where

/-- The extracted inner loop on `crc ^ b`, lowered (a failure reads as `0`; never reached). -/
noncomputable def extStepBits (c b : BitVec 8) : BitVec 8 :=
  match (crc8.crc8_loop0_loop0 { start := 0#i32, «end» := 8#i32 } (⟨c ^^^ b⟩ : Std.U8)).match with
  | .ok r => r.bv
  | _ => 0

/-- The extracted `TABLE` lookup at `crc ^ b` (an out-of-range index reads as `0`; never reached,
by `table_index`). -/
def extStepTable (c b : BitVec 8) : BitVec 8 :=
  match crc8.TABLE.val[(c ^^^ b).toNat]? with
  | some v => v.bv
  | none => 0

/-- The extracted bitwise `crc8` on the slice holding `bs`, lowered; the model fold beyond
`Usize.max` (see the module docstring). -/
noncomputable def extDigestBits (bs : List (BitVec 8)) : BitVec 8 :=
  if h : bs.length ≤ Usize.max then
    match (crc8.crc8 (bitsToSlice bs h)).match with
    | .ok r => r.bv
    | _ => 0
  else FramedChannel.Crc8.crc8Bits bs

/-- The extracted `crc8_table` on the slice holding `bs`, lowered; the model fold beyond
`Usize.max` (see the module docstring). -/
noncomputable def extDigestTable (bs : List (BitVec 8)) : BitVec 8 :=
  if h : bs.length ≤ Usize.max then
    match (crc8.crc8_table (bitsToSlice bs h)).match with
    | .ok r => r.bv
    | _ => 0
  else FramedChannel.Crc8.crc8Table bs

noncomputable instance instChecksumModelExtractedBitwise : ChecksumModel ExtractedBitwise where
  step := extStepBits
  seed := 0
  digest := extDigestBits

noncomputable instance instChecksumModelExtractedTabled : ChecksumModel ExtractedTabled where
  step := extStepTable
  seed := 0
  digest := extDigestTable

end FramedChannel.Bridge.crc8
