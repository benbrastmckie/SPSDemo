-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Model.VecQueue.Defs

/-!
# Model/VecQueue/Theorems: a second bounded queue

`[HAND-WRITTEN: model; bridged]` -- a list-backed bounded queue, mirrored in Rust by
`rust/src/queue.rs`'s `VecQueue<T>` field for field. It exists so that the interface in
`Spec/Queue.lean` has more than one instance: a theorem proved from the laws alone, such as
`Channel.deliver_spec`, is then used unchanged at both queues (substitution `Channel[VQ/BQ]`).

The representation is the logical contents itself plus a bound. No invariant subtype is needed
(contrast `RingBuffer.BQ`): `push` refuses once `cap ≤ items.length`, so every value reachable by
`push` stays within the bound and the laws hold on every value of `VQ α` as stated.

## Rust to Lean field mapping (`rust/src/queue.rs`'s `VecQueue<T>`)

| Rust `VecQueue<T>`  | Lean `VQ α`         | Note                                        |
|---------------------|---------------------|---------------------------------------------|
| `items: Vec<T>`     | `items : List α`    | the logical contents                        |
| `cap: usize`        | `cap : Nat`         | the bound                                   |
| `push -> Err(Full)` | `push = .fail`      | when `cap <= items.len()`                   |
| `push -> Ok(())`    | `push = .ok q'`     | else append at the back                     |
| `pop -> None`       | `pop = .fail`       | when empty                                  |
| `pop -> Some(x)`    | `pop = .ok (x, q')` | else remove from the front                  |

One recorded difference between the queues: `RingBuffer::with_capacity(0)` rounds a zero capacity
up to one (`0 < cap` is part of its invariant); `VecQueue::with_capacity(0)` does not, matching
`VQ`, which carries no such invariant.

Both instances are named (`instQueueModel`, `instBoundedQueueLaws`) so that the refinement
certificate can be registered by a stable name in `Registry.lean`.
-/

namespace FramedChannel.VecQueue

/-- The refinement certificate: `VQ` is a `BoundedQueue`, all six laws. `[PROVED: kernel]` -/
instance instBoundedQueueLaws (α : Type) : BoundedQueueLaws (VQ α) α where
  push_law q x h := by
    change ¬ (decide (q.cap ≤ q.items.length) = true) at h
    simp only [decide_eq_true_eq] at h
    exact ⟨{ q with items := q.items ++ [x] }, by simp [QueueModel.push, VQ.push, h], rfl⟩
  pop_law q h := by
    change ¬ q.items.isEmpty = true at h
    cases hq : q.items with
    | nil => simp [hq] at h
    | cons x xs => exact ⟨x, { q with items := xs }, by simp [QueueModel.pop, VQ.pop, hq], hq⟩
  full_law q x h := by
    change decide (q.cap ≤ q.items.length) = true at h
    simp only [decide_eq_true_eq] at h
    simp [QueueModel.push, VQ.push, h]
  empty_law q h := by
    change q.items.isEmpty = true at h
    cases hq : q.items with
    | nil => simp [QueueModel.pop, VQ.pop, hq]
    | cons x xs => simp [hq] at h
  not_full_of_lt q h := by
    change q.items.length < q.cap at h
    change ¬ (decide (q.cap ≤ q.items.length) = true)
    simp only [decide_eq_true_eq]; omega
  push_capacity q x q' h := by
    change VQ.push q x = .ok q' at h
    unfold VQ.push at h
    split at h
    · exact absurd h (by simp)
    · simp only [Result.ok.injEq] at h; subst h; rfl

ladder_record% instBoundedQueueLaws instance

/-- Bounds: a successful push leaves the item count within the capacity -- the counterpart of
`RingBuffer.push_bounded` and of `VecQueue::push`'s guard. `[PROVED: kernel]` -/
theorem push_bounded (α : Type) (q q' : VQ α) (x : α) (h : q.push x = .ok q') :
    q'.items.length ≤ q'.cap := by
  rung grind =>
    simp only [VQ.push] at *
    grind

#print axioms push_bounded
#print axioms instBoundedQueueLaws

end FramedChannel.VecQueue
