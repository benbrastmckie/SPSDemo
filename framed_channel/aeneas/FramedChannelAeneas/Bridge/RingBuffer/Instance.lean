-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Instance
import FramedChannelAeneas.Bridge.RingBuffer.Refinement

/-!
# Bridge/RingBuffer/Instance: `BoundedQueueLaws` on the extracted ring buffer

`[EXTRACTED: aeneas + bridge]` -- the specification's bounded-queue laws, instantiated
with the *extracted* ring buffer as the carrier.

`ExtractedRB α dflt cln` is `Bridge/Queue/Instance.lean`'s `Ext` at the extracted `BoundedQueue`
record of `rust/src/ring_buffer.rs` and the relation `toModel s = q.1` that `sim`
(`Refinement.lean` beside this file) is stated over. Its values are the extracted buffers whose
abstraction satisfies the model's invariant (`carrier_iff_inv`): the abstracted invariant, read on
the machine representation. Its `push`, `pop`, `full`, `empty` and `capacity` are the extracted
functions.

`instBoundedQueueLaws_extracted` is `QueueSim.boundedQueueLaws` at `sim`. This is the
one place the `CloneIsId` assumption (`Bridge/Queue/Traits.lean`) enters the instance: the extracted
`get` clones the element it reads, so the extracted `pop` returns the stored value only for an
identity `Clone`.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.ring_buffer
open framed_channel

variable {α : Type}

/-- The carrier condition is exactly the model's invariant on the abstraction. -/
theorem carrier_iff_inv [Inhabited α] (s : ring_buffer.RingBuffer α) :
    (∃ q : FramedChannel.RingBuffer.BQ α, toModel s = q.1) ↔ (toModel s).Inv :=
  ⟨fun ⟨q, hq⟩ => hq ▸ q.2, fun h => ⟨⟨toModel s, h⟩, rfl⟩⟩

/-- The simulation relation `toModel s = q.1` is functional: `BQ` is a subtype. -/
theorem rel_functional [Inhabited α] :
    ∀ (s : ring_buffer.RingBuffer α) (q q' : FramedChannel.RingBuffer.BQ α),
      toModel s = q.1 → toModel s = q'.1 → q = q' :=
  fun _ _ _ h1 h2 => Subtype.ext (h1.symm.trans h2)

/-- The extracted ring buffer satisfies all six bounded-queue laws, on its own extracted carrier,
for any `Default` record and any `Clone` record with `CloneIsId`.
`[EXTRACTED: aeneas + bridge]` -/
theorem instBoundedQueueLaws_extracted [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) (hcln : CloneIsId cln) :
    BoundedQueueLaws (ExtractedRB α dflt cln) α :=
  (sim dflt cln hcln).boundedQueueLaws rel_functional

end FramedChannel.Bridge.ring_buffer

#print axioms FramedChannel.Bridge.ring_buffer.carrier_iff_inv
#print axioms FramedChannel.Bridge.ring_buffer.rel_functional
#print axioms FramedChannel.Bridge.ring_buffer.instBoundedQueueLaws_extracted
