-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.VecQueue.Defs

/-!
# FramedChannelAeneasChallenge.VecQueue: approved statements (extracted list-backed queue)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/VecQueue/{Refinement,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.vec_queue
open framed_channel
variable {α : Type}

/-- Error agreement: at the bound the extracted `push` returns `Err(Full)` and keeps the queue. -/
theorem push_full (cln : core.clone.Clone α) (s : queue.VecQueue α) (x : α)
    (h : (toModel s).cap ≤ (toModel s).items.length) :
    queue.VecQueue.push cln s x ⦃ p => p = (.Err (), s) ⦄ := sorry

/-- Refinement: below the bound the extracted `push` succeeds and abstracts to the model's `push`.
-/
theorem push_refines (cln : core.clone.Clone α) (s : queue.VecQueue α) (x : α)
    (h : ¬ (toModel s).cap ≤ (toModel s).items.length) :
    queue.VecQueue.push cln s x
      ⦃ p => p.1 = .Ok () ∧ (toModel s).push x = .ok (toModel p.2) ⦄ := sorry

/-- Error agreement: on an empty queue the extracted `pop` returns `None` and keeps the queue. -/
theorem pop_empty (cln : core.clone.Clone α) (s : queue.VecQueue α)
    (h : (toModel s).items = []) :
    queue.VecQueue.pop cln s ⦃ p => p = (none, s) ⦄ := sorry

/-- Refinement: on a non-empty queue the extracted `pop` succeeds and abstracts to the model's
`pop`. -/
theorem pop_refines (cln : core.clone.Clone α) (s : queue.VecQueue α)
    (h : (toModel s).items ≠ []) :
    queue.VecQueue.pop cln s
      ⦃ p => ∃ y, p.1 = some y ∧ (toModel s).pop = .ok (y, toModel p.2) ⦄ := sorry

/-- The extracted `capacity` is the model's bound. -/
theorem capacity_agrees (cln : core.clone.Clone α) (s : queue.VecQueue α) :
    queue.VecQueue.capacity cln s ⦃ c => c.val = (toModel s).cap ⦄ := sorry

/-- The extracted `len` is the model's item count. -/
theorem len_agrees (cln : core.clone.Clone α) (s : queue.VecQueue α) :
    queue.VecQueue.len cln s ⦃ n => n.val = (toModel s).items.length ⦄ := sorry

/-- The extracted `is_full` is the model's bound check. -/
theorem is_full_agrees (cln : core.clone.Clone α) (s : queue.VecQueue α) :
    queue.VecQueue.is_full cln s
      ⦃ b => b = decide ((toModel s).cap ≤ (toModel s).items.length) ⦄ := sorry

/-- The extracted `is_empty` is the model's emptiness check. -/
theorem is_empty_agrees (cln : core.clone.Clone α) (s : queue.VecQueue α) :
    queue.VecQueue.is_empty cln s ⦃ b => b = (toModel s).items.isEmpty ⦄ := sorry

/-- The extracted `BoundedQueue` record instance of the list-backed queue simulates the model
`VQ`, related by `toModel s = q`, at every `Clone` record: the per-component input to every
generic transport theorem in `Bridge/Queue/Transport.lean`. -/
theorem sim (cln : core.clone.Clone α) :
    QueueSim (queue.VecQueue α) (FramedChannel.VecQueue.VQ α) α
      (queue.VecQueue.Insts.Framed_channelQueueBoundedQueue cln)
      (fun s q => toModel s = q) := sorry

/-- `push_law` for the extracted code, derived from the generic transport: below the bound the
extracted `push` succeeds and appends to the model's items. -/
theorem push_law_extracted (cln : core.clone.Clone α) (s : queue.VecQueue α) (x : α)
    (h : ¬ (toModel s).cap ≤ (toModel s).items.length) :
    queue.VecQueue.push cln s x
      ⦃ p => p.1 = .Ok () ∧ (toModel p.2).items = (toModel s).items ++ [x] ⦄ := sorry

/-- `pop_law` for the extracted code, derived from the generic transport: on a non-empty queue the
extracted `pop` succeeds and removes the front of the model's items. -/
theorem pop_law_extracted (cln : core.clone.Clone α) (s : queue.VecQueue α)
    (h : (toModel s).items ≠ []) :
    queue.VecQueue.pop cln s
      ⦃ p => ∃ y, p.1 = some y ∧ (toModel s).items = y :: (toModel p.2).items ⦄ := sorry
end FramedChannel.Bridge.vec_queue

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.vec_queue
open framed_channel
variable {α : Type}

/-- The extracted list-backed queue satisfies all six bounded-queue laws, on its own extracted
carrier, at every `Clone` record. -/
theorem instBoundedQueueLaws_extracted (cln : core.clone.Clone α) :
    BoundedQueueLaws (ExtractedVQ α cln) α := sorry
end FramedChannel.Bridge.vec_queue
