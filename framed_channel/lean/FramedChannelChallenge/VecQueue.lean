-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Model.VecQueue.Defs

/-!
# FramedChannelChallenge.VecQueue: approved statements (list-backed queue model)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Model/VecQueue/Theorems.lean`. See `lean/FramedChannelChallenge.lean` for what a
Challenge module is and what the gate checks.
-/

namespace FramedChannel.VecQueue

/-- The refinement certificate: `VQ` is a `BoundedQueue`, all six laws. -/
instance instBoundedQueueLaws (α : Type) : BoundedQueueLaws (VQ α) α := sorry

/-- Bounds: a successful push leaves the item count within the capacity -- the counterpart of
`RingBuffer.push_bounded` and of `VecQueue::push`'s guard. -/
theorem push_bounded (α : Type) (q q' : VQ α) (x : α) (h : q.push x = .ok q') :
    q'.items.length ≤ q'.cap := sorry
end FramedChannel.VecQueue
