-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Defs

/-!
# FramedChannelAeneasChallenge.Queue: approved statements (queue transport, Clone assumption)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/Queue/{Traits,Transport,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge
variable {α : Type}

/-- The `Clone` record the extraction actually uses for frames, the derived `Clone` of `Vec<u8>`
(`CloneallocvecVec` over `CloneU8`), satisfies the assumption. This is proved, so no bridge theorem
about a queue of frames carries `CloneIsId` as a hypothesis. -/
theorem cloneVecU8_isId : CloneIsId (core.clone.CloneallocvecVec core.clone.CloneU8) := sorry
end FramedChannel.Bridge

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge
open framed_channel

/-- `push_law` at the extracted record: a push on a non-full queue succeeds and appends `x` to the
related model's contents. -/
theorem push_law_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (x : T) (hR : R s q) (h : ¬ QueueModel.full (Q := Q) (α := T) q) :
    inst.push s x ⦃ p => p.1 = .Ok () ∧ ∃ q', R p.2 q' ∧
      QueueModel.toList (Q := Q) (α := T) q' = QueueModel.toList (Q := Q) (α := T) q ++ [x] ⦄ := sorry

/-- `pop_law` at the extracted record: a pop on a non-empty queue returns the related model's
front element and its remainder. -/
theorem pop_law_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (hR : R s q) (h : ¬ QueueModel.empty (Q := Q) (α := T) q) :
    inst.pop s ⦃ p => ∃ y q', p.1 = some y ∧ R p.2 q' ∧
      QueueModel.toList (Q := Q) (α := T) q = y :: QueueModel.toList (Q := Q) (α := T) q' ⦄ := sorry

/-- `full_law` at the extracted record: on a full queue the extracted push refuses and keeps the
state, exactly where the model's push fails. -/
theorem full_law_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (x : T) (hR : R s q) (h : QueueModel.full (Q := Q) (α := T) q) :
    inst.push s x ⦃ p => p = (.Err (), s) ∧
      QueueModel.push q x = (.fail : FramedChannel.Result Q) ⦄ := sorry

/-- `empty_law` at the extracted record: on an empty queue the extracted pop returns `none` and
keeps the state, exactly where the model's pop fails. -/
theorem empty_law_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (hR : R s q) (h : QueueModel.empty (Q := Q) (α := T) q) :
    inst.pop s ⦃ p => p = (none, s) ∧
      QueueModel.pop q = (.fail : FramedChannel.Result (T × Q)) ⦄ := sorry

/-- `not_full_of_lt` at the extracted record: room below the capacity means the extracted
`is_full` reports `false`. -/
theorem not_full_of_lt_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (hR : R s q)
    (h : (QueueModel.toList (Q := Q) (α := T) q).length < QueueModel.capacity (Q := Q) (α := T) q) :
    inst.is_full s ⦃ b => b = false ⦄ := sorry

/-- `push_capacity` at the extracted record: a successful extracted push is related to a model
state of the same capacity. -/
theorem push_capacity_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (x : T) (hR : R s q) (h : ¬ QueueModel.full (Q := Q) (α := T) q) :
    inst.push s x ⦃ p => ∃ q', R p.2 q' ∧
      QueueModel.capacity (Q := Q) (α := T) q' = QueueModel.capacity (Q := Q) (α := T) q ⦄ := sorry
end FramedChannel.Bridge

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge
open framed_channel
variable {S Q T : Type} [QueueModel Q T] {inst : queue.BoundedQueue S T} {R : S → Q → Prop}

/-- Every simulating extracted record, read on its extracted carrier, satisfies all six bounded-queue
laws, provided the simulation relation is functional. Each law is the matching transport theorem of
`Bridge/Queue/Transport.lean`. -/
theorem QueueSim.boundedQueueLaws [BoundedQueueLaws Q T] (hsim : QueueSim S Q T inst R)
    (hfun : ∀ s q q', R s q → R s q' → q = q') : BoundedQueueLaws (Ext S Q T inst R) T := sorry
end FramedChannel.Bridge
