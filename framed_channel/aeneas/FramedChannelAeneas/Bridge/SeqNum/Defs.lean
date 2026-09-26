-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs
import FramedChannel.Model.SeqNum.Defs

/-!
# Bridge/SeqNum/Defs: the extracted sequence number, read as the model's `BitVec 16`

`[HAND-WRITTEN]` -- the definitions the serial-number refinement theorems
(`Instance.lean` beside this file) are stated over.

## The abstraction is an equality of representations, not a projection

The extracted carrier is `structure seq_num.SeqNum where value : Std.U16`, and a `Std.U16` carries
its bit vector as `.bv`. The model's carrier is `BitVec 16` itself (`Model/SeqNum/Defs.lean`'s
recorded representation decision), so `toModel` is `s.value.bv` -- a field read, with no modulus,
no range side condition and no information lost. `toModel_inj` below is the formal statement of
that: the abstraction is a bijection, `ofModel` its inverse. This is the payoff Decision 1 of the
plan predicted for choosing `BitVec 16` over `Nat` with an explicit modulus, and it is why every
wraparound obligation in `Instance.lean` closes by Aeneas's own
`core.num.U16.wrapping_add_bv_eq` / `wrapping_sub_bv_eq`, which are stated directly as `BitVec 16`
arithmetic on `.bv`.

## The lowered operations, and why they are total

Every extracted `SeqNum` operation is failure-free: `new` and `get` are a bare `ok`, and `succ`,
`add`, `dist` and `lt` go through `core.num.U16.wrapping_add` / `wrapping_sub`, which are pure
`U16 -> U16 -> U16` functions in Aeneas's library rather than `Result`-valued ones -- wrapping
arithmetic cannot overflow. The `ext*` definitions below lower each call with `Result.match`, in the
shape `Bridge/Crc8/Defs.lean` uses, and the `*_refines` theorems of `Instance.lean` prove the
lowering is faithful on the success path *and* that there is no other path.

`instSerialModelExtracted` instantiates the interface **directly at the extracted carrier**, as the
plan's step 9.5 test requires: `SeqNum` dispatches through no trait and no composite is proved
generic over it, so no `SerialSim` is owed and none is built.

Every definition a registered `SeqNum` bridge statement mentions is here, so
`FramedChannelAeneasChallenge.SeqNum` can import them without importing a registered theorem.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.seq_num
open framed_channel

/-- The abstraction function: the extracted sequence number's machine word, as its bit vector. -/
def toModel (s : seq_num.SeqNum) : BitVec 16 := s.value.bv

/-- The inverse: a model sequence number as the extracted carrier. -/
def ofModel (b : BitVec 16) : seq_num.SeqNum := ⟨⟨b⟩⟩

/-- The extracted successor, lowered (it cannot fail; `succ_refines` proves so). -/
def extSucc (s : seq_num.SeqNum) : seq_num.SeqNum :=
  match (seq_num.SeqNum.succ s).match with
  | .ok r => r
  | _ => s

/-- The extracted bounded increment, lowered (it cannot fail; `add_refines` proves so). -/
def extAdd (s : seq_num.SeqNum) (n : Std.U16) : seq_num.SeqNum :=
  match (seq_num.SeqNum.add s n).match with
  | .ok r => r
  | _ => s

/-- The extracted forward distance, lowered (it cannot fail; `dist_refines` proves so). -/
def extDist (a b : seq_num.SeqNum) : Std.U16 :=
  match (seq_num.SeqNum.dist a b).match with
  | .ok d => d
  | _ => 0#u16

/-- The extracted serial comparison, lowered (it cannot fail; `lt_refines` proves so). -/
def extLt (a b : seq_num.SeqNum) : Bool :=
  match (seq_num.SeqNum.lt a b).match with
  | .ok r => r
  | _ => false

/-- Whether §3.2's comparison is defined on this extracted pair: the distance is not exactly the
extracted `HALF`. The model's `defined` read through the extraction, not a second spelling. -/
def extDefined (a b : seq_num.SeqNum) : Bool := extDist a b != seq_num.HALF

/-- `SerialModel` at the extracted carrier: the interface's operations are the extracted Rust's,
lowered. `space` is the model's own `FramedChannel.SeqNum.space`, not a fresh literal. -/
instance instSerialModelExtracted : SerialModel seq_num.SeqNum where
  zero := ⟨0#u16⟩
  succ := extSucc
  lt := extLt
  defined := extDefined
  space := FramedChannel.SeqNum.space

end FramedChannel.Bridge.seq_num
