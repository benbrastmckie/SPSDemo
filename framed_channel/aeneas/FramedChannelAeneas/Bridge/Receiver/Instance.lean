-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Receiver.Refinement
import FramedChannelAeneas.Bridge.RingBuffer.Instance
import FramedChannelAeneas.Bridge.VecQueue.Instance

/-!
# Bridge/Receiver/Instance: substitution `Receiver[RB/VQ]` on the extracted code

`[EXTRACTED: aeneas + bridge]` -- the theorems of `Refinement.lean`, proved once over any lawful
extracted queue record, instantiated at the two extracted queues with no reproof. This is the
substitution row exercised at a receive path: `Channel[VQ/BQ]` was the first and
`StuffedChannel[VQ/BQ]` the second, and the point of repeating it is that the generic proof was
written once and neither instantiation reopens it.

* the ring buffer: `rbRecord`, the record `receiver.ReceiverRingBufferVecU8.new` builds, with the
  simulation `sim` at the derived `Clone` of `Vec<u8>`, whose `CloneIsId` is *proved*
  (`cloneVecU8_isId`), and `Default` for `Vec<u8>`, which needs no hypothesis;
* `VecQueue`: `vqRecord`, with `sim`, which needs no trait hypothesis at all. No `rust/src` code
  builds a `VecQueue` receiver; the instantiation happens here, as it does in `rust/tests`.

The instantiated theorems carry no `QueueSim`, `CloneIsId` or `Default` hypothesis. `cloneVecU8_isId`
is the one name of Phase 10's reuse list that is *not* in any `Defs` module: it is a hypothesis
argument, threaded here exactly as `Bridge/StuffedChannel/Instance.lean` threads it.

The constructor claims start at the Rust constructors (`Receiver::new`, `Receiver::with_queue`),
through each queue's `with_capacity_rel`, so no idle state is assumed.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.receiver
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.channel (ExtQ FrameVec frameClone frameDefault rbRecord vqRecord)
open FramedChannel.Receiver (Rcv)

section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hfun

/-- `Receiver::with_queue` over any record whose `with_capacity` returns a state related to an empty
model queue: the new receiver is related to an idle specification receiver -- no buffered run, no
drops, nothing accepted. `[EXTRACTED: aeneas + bridge]` -/
theorem with_queue_idle
    (hwc : ∀ cap, inst.with_capacity cap ⦃ s => ∃ q, R s q ∧
      QueueModel.toList (Q := Q) (α := alloc.vec.Vec Std.U8) q = [] ⦄)
    (cap : Std.Usize) :
    receiver.Receiver.with_queue inst cap ⦃ c =>
      ∃ m : Rcv (ExtQ S Q inst R), RcvRel c m ∧ m.buf = [] ∧ m.dropped = 0 ∧
        QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out = [] ⦄ := by
  unfold receiver.Receiver.with_queue
  step with hwc cap as ⟨q, s, hq, hl⟩
  have hl' := extToList_eq (T := alloc.vec.Vec Std.U8) (inst := inst) hfun ⟨s, q, hq⟩ q hq
  refine ⟨⟨⟨s, q, hq⟩, [], 0⟩, ⟨rfl, ?_, ?_⟩, rfl, rfl, ?_⟩
  · simp [bytesOf]
  · simp
  · rw [hl', hl]
end

/-- `Receiver::new` (the ring buffer receiver) starts idle, at every capacity.
`[EXTRACTED: aeneas + bridge]` -/
theorem new_idle_RB (cap : Std.Usize) :
    receiver.ReceiverRingBufferVecU8.new cap ⦃ c => ∃ m : RcvRB, RcvRel c m ∧ m.buf = [] ∧
      m.dropped = 0 ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := by
  unfold receiver.ReceiverRingBufferVecU8.new
  apply with_queue_idle ring_buffer.rel_functional
  intro cap
  apply WP.spec_mono (ring_buffer.with_capacity_rel frameDefault frameClone cloneVecU8_isId
    (alloc.vec.Vec.new Std.U8) rfl cap)
  rintro s ⟨hinv, hlen, -⟩
  refine ⟨⟨ring_buffer.toModel s, hinv⟩, rfl, ?_⟩
  show FramedChannel.RingBuffer.contents (ring_buffer.toModel s) = []
  simp [FramedChannel.RingBuffer.contents, hlen]

/-- `Receiver::with_queue` at the `VecQueue` record starts idle. `[EXTRACTED: aeneas + bridge]` -/
theorem with_queue_idle_VQ (cap : Std.Usize) :
    receiver.Receiver.with_queue vqRecord cap ⦃ c => ∃ m : RcvVQ, RcvRel c m ∧ m.buf = [] ∧
      m.dropped = 0 ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := by
  apply with_queue_idle vec_queue.rel_functional
  intro cap
  apply WP.spec_mono (vec_queue.with_capacity_rel frameClone cap)
  intro s hs
  exact ⟨_, hs, rfl⟩

/-- `feed_refines` at the extracted ring buffer: no simulation hypothesis remains.
`[EXTRACTED: aeneas + bridge]` -/
theorem feed_refines_RB (c : receiver.Receiver (ring_buffer.RingBuffer FrameVec)) (m : RcvRB)
    (bytes : Slice Std.U8) (hR : RcvRel c m) (hnw : NoWideRun bytes m)
    (hbufw : c.buf.val.length + bytes.val.length ≤ Usize.max)
    (hdropw : c.dropped.val + bytes.val.length ≤ Usize.max) :
    receiver.Receiver.feed rbRecord c bytes ⦃ c' =>
      RcvRel c' (FramedChannel.Receiver.feed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := FrameVec)
        FramedChannel.Stuff.marker m (bytesOf bytes.val)) ⦄ :=
  feed_refines (ring_buffer.sim frameDefault frameClone cloneVecU8_isId)
    c m bytes hR hnw hbufw hdropw

/-- The same proof at the extracted `VecQueue`, with no reproof. `[EXTRACTED: aeneas + bridge]` -/
theorem feed_refines_VQ (c : receiver.Receiver (queue.VecQueue FrameVec)) (m : RcvVQ)
    (bytes : Slice Std.U8) (hR : RcvRel c m) (hnw : NoWideRun bytes m)
    (hbufw : c.buf.val.length + bytes.val.length ≤ Usize.max)
    (hdropw : c.dropped.val + bytes.val.length ≤ Usize.max) :
    receiver.Receiver.feed vqRecord c bytes ⦃ c' =>
      RcvRel c' (FramedChannel.Receiver.feed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := FrameVec)
        FramedChannel.Stuff.marker m (bytesOf bytes.val)) ⦄ :=
  feed_refines (vec_queue.sim frameClone) c m bytes hR hnw hbufw hdropw

/-- `poll_refines` at the extracted ring buffer. `[EXTRACTED: aeneas + bridge]` -/
theorem poll_refines_RB (c : receiver.Receiver (ring_buffer.RingBuffer FrameVec)) (m : RcvRB)
    (hR : RcvRel c m) :
    receiver.Receiver.poll rbRecord c ⦃ o c' =>
      (∀ y m', FramedChannel.Receiver.poll (E := FrameVec) m = .ok (y, m') →
        o = some y ∧ RcvRel c' m') ∧
      (FramedChannel.Receiver.poll (E := FrameVec) m = .fail → o = none ∧ c' = c) ⦄ :=
  poll_refines (ring_buffer.sim frameDefault frameClone cloneVecU8_isId) c m hR

/-- The same proof at the extracted `VecQueue`, with no reproof. `[EXTRACTED: aeneas + bridge]` -/
theorem poll_refines_VQ (c : receiver.Receiver (queue.VecQueue FrameVec)) (m : RcvVQ)
    (hR : RcvRel c m) :
    receiver.Receiver.poll vqRecord c ⦃ o c' =>
      (∀ y m', FramedChannel.Receiver.poll (E := FrameVec) m = .ok (y, m') →
        o = some y ∧ RcvRel c' m') ∧
      (FramedChannel.Receiver.poll (E := FrameVec) m = .fail → o = none ∧ c' = c) ⦄ :=
  poll_refines (vec_queue.sim frameClone) c m hR

end FramedChannel.Bridge.receiver

#print axioms FramedChannel.Bridge.receiver.with_queue_idle
#print axioms FramedChannel.Bridge.receiver.new_idle_RB
#print axioms FramedChannel.Bridge.receiver.with_queue_idle_VQ
#print axioms FramedChannel.Bridge.receiver.feed_refines_RB
#print axioms FramedChannel.Bridge.receiver.feed_refines_VQ
#print axioms FramedChannel.Bridge.receiver.poll_refines_RB
#print axioms FramedChannel.Bridge.receiver.poll_refines_VQ
