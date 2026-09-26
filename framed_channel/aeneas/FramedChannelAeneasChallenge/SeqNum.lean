-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.SeqNum.Defs

/-!
# FramedChannelAeneasChallenge.SeqNum: approved statements (extracted RFC 1982 sequence number)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/SeqNum/Instance.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.

**Read the hypotheses: there are none.** Every triple below is unconditional, unlike the varint and
stuffing codecs' encode refinements, which must carry a `Vec::push` overflow bound. The extracted
`SeqNum` operations go through `core.num.U16.wrapping_add` / `wrapping_sub`, which are pure
functions in Aeneas's library rather than `Result`-valued ones, so wraparound is the definition and
not a failure to exclude. RFC 1982 §3.1's `0 < n < 2 ^ 15` restricts the *claim*
`FramedChannel.SeqNum.lt_add`, not this operation.

**There is no transitivity statement, and no `SerialLaws` field for one.**
`lean/FramedChannel/Evidence/Countermodels.lean` refutes it in the kernel at `(0, 20000, 40000)`.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.seq_num
open framed_channel

/-- The extracted `HALF` const is `2 ^ 15`. The extraction emits a `pub const` as an `irreducible`
definition of its own, so it is a selection candidate in its own right and needs a statement about
it exactly as each function does. -/
theorem HALF_val : seq_num.HALF.val = 32768 := sorry

/-- The extracted constructor stores exactly the word it is given. -/
theorem new_refines (v : Std.U16) :
    seq_num.SeqNum.new v ⦃ s => toModel s = v.bv ⦄ := sorry

/-- The extracted accessor returns exactly the stored word, so `new` and `get` are inverse. -/
theorem get_refines (s : seq_num.SeqNum) :
    seq_num.SeqNum.get s ⦃ v => v.bv = toModel s ⦄ := sorry

/-- The extracted successor is the model's `succ` under the abstraction, wraparound included, with
no failure case. -/
theorem succ_refines (s : seq_num.SeqNum) :
    seq_num.SeqNum.succ s ⦃ r => toModel r = FramedChannel.SeqNum.succ (toModel s) ⦄ := sorry

/-- The extracted bounded increment is the model's `add` under the abstraction, on every
increment. -/
theorem add_refines (s : seq_num.SeqNum) (n : Std.U16) :
    seq_num.SeqNum.add s n ⦃ r => toModel r = FramedChannel.SeqNum.add (toModel s) n.bv ⦄ := sorry

/-- The extracted forward distance is the model's `dist` under the abstraction. -/
theorem dist_refines (a b : seq_num.SeqNum) :
    seq_num.SeqNum.dist a b ⦃ d => d.bv = FramedChannel.SeqNum.dist (toModel a) (toModel b) ⦄ :=
  sorry

/-- The extracted serial comparison is the model's `lt` under the abstraction: the machine's
zero-test-then-compare shape agrees with the model's conjunction on every pair. -/
theorem lt_refines (a b : seq_num.SeqNum) :
    seq_num.SeqNum.lt a b ⦃ r => r = FramedChannel.SeqNum.lt (toModel a) (toModel b) ⦄ := sorry

/-- The refinement certificate as an interface instance, at the extracted carrier itself rather than
at a component tag: `SerialModel` is indexed by the representation. -/
instance instSerialLaws_extracted : SerialLaws seq_num.SeqNum := sorry

end FramedChannel.Bridge.seq_num
