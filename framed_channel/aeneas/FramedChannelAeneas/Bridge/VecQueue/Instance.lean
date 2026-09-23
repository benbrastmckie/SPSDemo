-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Instance
import FramedChannelAeneas.Bridge.VecQueue.Refinement

/-!
# Bridge/VecQueue/Instance: `BoundedQueueLaws` on the extracted list-backed queue

`[EXTRACTED: aeneas + bridge]` -- the specification's bounded-queue laws, instantiated
with the *extracted* `VecQueue` as the carrier: the second extracted instance of the one
interface, beside `Bridge/RingBuffer/Instance.lean`'s.

`ExtractedVQ α cln` is `Bridge/Queue/Instance.lean`'s `Ext` at the extracted `BoundedQueue` record
of `rust/src/queue.rs`'s `VecQueue<T>` and the relation `toModel s = q` that `sim`
(`Refinement.lean` beside this file) is stated over. The relation is the graph of a total
function, so every extracted state lies on the carrier. `instBoundedQueueLaws_extracted` is
`QueueSim.boundedQueueLaws` at `sim`, and it holds at every `Clone` record: no trait
assumption is needed, because no bridged operation clones.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.vec_queue
open framed_channel

variable {α : Type}

/-- The simulation relation `toModel s = q` is functional. -/
theorem rel_functional :
    ∀ (s : queue.VecQueue α) (q q' : FramedChannel.VecQueue.VQ α),
      toModel s = q → toModel s = q' → q = q' :=
  fun _ _ _ h1 h2 => h1.symm.trans h2

/-- The extracted list-backed queue satisfies all six bounded-queue laws, on its own extracted
carrier, at every `Clone` record. `[EXTRACTED: aeneas + bridge]` -/
theorem instBoundedQueueLaws_extracted (cln : core.clone.Clone α) :
    BoundedQueueLaws (ExtractedVQ α cln) α :=
  (sim cln).boundedQueueLaws rel_functional

end FramedChannel.Bridge.vec_queue

#print axioms FramedChannel.Bridge.vec_queue.rel_functional
#print axioms FramedChannel.Bridge.vec_queue.instBoundedQueueLaws_extracted
