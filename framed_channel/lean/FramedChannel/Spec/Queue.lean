-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Result

/-!
# Spec/Queue: the bounded-queue interface, `QueueModel` (L0) and `BoundedQueueLaws` (L1)

The L0/L1 split, with the bounded operations returning `Result`, an abstraction function `toList`,
and a `capacity` that lets a client (the channel in `Composition/Channel/Theorems.lean`) state its own bound
check.

This module is specification only: it names no implementation. Its instances live in the model
layer (`Model/RingBuffer/Theorems.lean` on the invariant subtype `BQ`, `Model/VecQueue/Theorems.lean` on `VQ`), and
the extracted Rust reaches the laws through the bridge layer's `QueueSim`
(`aeneas/FramedChannelAeneas/Bridge/Queue/Transport.lean`), not through an instance of these classes.

An instance must satisfy the laws on *every* value of its carrier. That is why the ring buffer's
instance is stated on `{r : RingBuffer α // r.Inv}`: a raw `RingBuffer` violating `Inv` has
meaningless `contents`.
-/

namespace FramedChannel

/-- L0: the operations of a bounded queue over a representation `Q`. -/
class QueueModel (Q : Type) (α : Type) where
  /-- Append an element at the back, or refuse. -/
  push : Q → α → Result Q
  /-- Remove the front element, or refuse. -/
  pop : Q → Result (α × Q)
  /-- The abstraction function: the queued elements, front first. -/
  toList : Q → List α
  /-- Whether `push` must refuse. -/
  full : Q → Bool
  /-- Whether `pop` must refuse. -/
  empty : Q → Bool
  /-- The bound on the number of queued elements. -/
  capacity : Q → Nat

/-- L1: the laws a bounded-queue implementation must satisfy, stated through `toList`. -/
class BoundedQueueLaws (Q : Type) (α : Type) [QueueModel Q α] : Prop where
  /-- A push on a non-full queue succeeds and appends the element. -/
  push_law : ∀ (q : Q) (x : α), ¬ QueueModel.full (Q := Q) (α := α) q →
    ∃ q' : Q, QueueModel.push q x = .ok q' ∧
      QueueModel.toList (Q := Q) (α := α) q' = QueueModel.toList (Q := Q) (α := α) q ++ [x]
  /-- A pop on a non-empty queue succeeds and removes the front element. -/
  pop_law : ∀ q : Q, ¬ QueueModel.empty (Q := Q) (α := α) q →
    ∃ (x : α) (q' : Q), QueueModel.pop q = .ok (x, q') ∧
      QueueModel.toList (Q := Q) (α := α) q = x :: QueueModel.toList (Q := Q) (α := α) q'
  /-- A push on a full queue refuses. -/
  full_law : ∀ (q : Q) (x : α), QueueModel.full (Q := Q) (α := α) q →
    QueueModel.push q x = (.fail : Result Q)
  /-- A pop on an empty queue refuses. -/
  empty_law : ∀ q : Q, QueueModel.empty (Q := Q) (α := α) q →
    QueueModel.pop q = (.fail : Result (α × Q))
  /-- Room below the capacity means not full. -/
  not_full_of_lt : ∀ q : Q, (QueueModel.toList (Q := Q) (α := α) q).length <
    QueueModel.capacity (Q := Q) (α := α) q → ¬ QueueModel.full (Q := Q) (α := α) q
  /-- `push` leaves the capacity unchanged. -/
  push_capacity : ∀ (q : Q) (x : α) (q' : Q), QueueModel.push q x = .ok q' →
    QueueModel.capacity (Q := Q) (α := α) q' = QueueModel.capacity (Q := Q) (α := α) q

end FramedChannel
