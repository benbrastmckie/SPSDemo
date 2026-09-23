-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Queue

/-!
# Model/VecQueue/Defs: the list-backed queue definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of `Model/VecQueue/Theorems.lean`: the
representation `VQ`, its operations and the `QueueModel` instance. It holds definitions only, so
that the Challenge module `FramedChannelChallenge.VecQueue` can import them without importing a
registered theorem.
-/

namespace FramedChannel.VecQueue

/-- A bounded FIFO queue stored front-to-back as a list, with capacity `cap`. -/
structure VQ (α : Type) where
  items : List α
  cap : Nat

/-- Append at the back; fail once the bound is reached. -/
def VQ.push {α : Type} (q : VQ α) (x : α) : Result (VQ α) :=
  if q.cap ≤ q.items.length then .fail else .ok { q with items := q.items ++ [x] }

/-- Remove from the front; fail when empty. -/
def VQ.pop {α : Type} (q : VQ α) : Result (α × VQ α) :=
  match q.items with
  | [] => .fail
  | x :: xs => .ok (x, { q with items := xs })

instance instQueueModel (α : Type) : QueueModel (VQ α) α where
  push := VQ.push
  pop := VQ.pop
  toList q := q.items
  full q := decide (q.cap ≤ q.items.length)
  empty q := q.items.isEmpty
  capacity q := q.cap

end FramedChannel.VecQueue
