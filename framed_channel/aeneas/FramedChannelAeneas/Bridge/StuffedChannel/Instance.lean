-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.StuffedChannel.Composite
import FramedChannelAeneas.Bridge.RingBuffer.Instance
import FramedChannelAeneas.Bridge.VecQueue.Instance

/-!
# Bridge/StuffedChannel/Instance: substitution `StuffedChannel[RB/VQ]` on the extracted code

`[EXTRACTED: aeneas + bridge]` -- the theorems of `Composite.lean`, proved once over any lawful
extracted queue record, instantiated at the two extracted queues with no reproof. This is the
substitution row exercised at a **second** composite: `Channel[VQ/BQ]` was the first, and the point
of repeating it here is that the generic proof was written once and neither instantiation reopens it.

* the ring buffer: `rbRecord`, the record `stuffed_channel.StuffedChannelRingBufferVecU8.new`
  builds, with the simulation `sim` at the derived `Clone` of `Vec<u8>`, whose `CloneIsId` is
  *proved* (`cloneVecU8_isId`), and `Default` for `Vec<u8>`, which needs no hypothesis;
* `VecQueue`: `vqRecord`, with `sim`, which needs no trait hypothesis at all. No `rust/src` code
  builds a `VecQueue` stuffed channel; the instantiation happens here, as it does in `rust/tests`.

The instantiated theorems carry no `QueueSim`, `CloneIsId` or `Default` hypothesis. The headline
chain `send_deliver_from_new_RB`/`_VQ` starts at the Rust constructors (`StuffedChannel::new`,
`StuffedChannel::with_queue`), through each queue's `with_capacity_rel`, so no idle state is assumed.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Bridge.channel (ExtQ FrameVec frameClone frameDefault rbRecord vqRecord)
open FramedChannel.Channel (Frame FrameCarrier FrameOK)
open FramedChannel.StuffedChannel (SChan SChanInv)

section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hfun

/-- `StuffedChannel::with_queue` over any record whose `with_capacity` returns a state related to an
empty model queue: the new channel is related to an idle specification channel. -/
theorem with_queue_idle
    (hwc : ∀ cap, inst.with_capacity cap ⦃ s => ∃ q, R s q ∧
      QueueModel.toList (Q := Q) (α := alloc.vec.Vec Std.U8) q = [] ⦄)
    (cap : Std.Usize) :
    stuffed_channel.StuffedChannel.with_queue inst cap ⦃ c =>
      ∃ m : SChan (ExtQ S Q inst R), SChanRel c m ∧
        SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) m [] ∧
        QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out = [] ⦄ := by
  unfold stuffed_channel.StuffedChannel.with_queue
  step with hwc cap as ⟨q, s, hq, hl⟩
  have hl' := extToList_eq (T := alloc.vec.Vec Std.U8) (inst := inst) hfun ⟨s, q, hq⟩ q hq
  refine ⟨⟨⟨s, q, hq⟩, [], 0⟩, ⟨rfl, ?_, ?_⟩, ⟨rfl, rfl, by simp, ?_⟩, ?_⟩
  · simp [bytesOf]
  · simp
  · simp only [hl', hl, List.length_nil, Nat.add_zero, Nat.zero_le]
  · rw [hl', hl]
end

/-- `StuffedChannel::new` (the ring buffer channel) starts idle: related to a specification channel
with no pending frame and an empty queue, at every capacity. `[EXTRACTED: aeneas + bridge]` -/
theorem new_idle_RB (cap : Std.Usize) :
    stuffed_channel.StuffedChannelRingBufferVecU8.new cap ⦃ c => ∃ m : SChanRB, SChanRel c m ∧
      SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) (E := FrameVec)
        m [] ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := by
  unfold stuffed_channel.StuffedChannelRingBufferVecU8.new
  apply with_queue_idle ring_buffer.rel_functional
  intro cap
  apply WP.spec_mono (ring_buffer.with_capacity_rel frameDefault frameClone cloneVecU8_isId
    (alloc.vec.Vec.new Std.U8) rfl cap)
  rintro s ⟨hinv, hlen, -⟩
  refine ⟨⟨ring_buffer.toModel s, hinv⟩, rfl, ?_⟩
  show FramedChannel.RingBuffer.contents (ring_buffer.toModel s) = []
  simp [FramedChannel.RingBuffer.contents, hlen]

/-- `StuffedChannel::with_queue` at the `VecQueue` record starts idle.
`[EXTRACTED: aeneas + bridge]` -/
theorem with_queue_idle_VQ (cap : Std.Usize) :
    stuffed_channel.StuffedChannel.with_queue vqRecord cap ⦃ c => ∃ m : SChanVQ, SChanRel c m ∧
      SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) (E := FrameVec)
        m [] ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := by
  apply with_queue_idle vec_queue.rel_functional
  intro cap
  apply WP.spec_mono (vec_queue.with_capacity_rel frameClone cap)
  intro s hs
  exact ⟨_, hs, rfl⟩

/-- `send_deliver_extracted` at the extracted ring buffer: no simulation, `CloneIsId` or `Default`
hypothesis remains. `[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_extracted_RB
    (c : stuffed_channel.StuffedChannel (ring_buffer.RingBuffer FrameVec)) (m : SChanRB)
    (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := FrameVec) m [])
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send rbRecord c payload ⦃ r c1 =>
      r = .Ok () →
        stuffed_channel.StuffedChannel.deliver rbRecord c1 ⦃ r2 c2 =>
          ∃ v, ∃ m2 : SChanRB, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧ SChanRel c2 m2 ∧
            QueueModel.toList (α := FrameVec) m2.out =
              QueueModel.toList (α := FrameVec) m.out ++
                [FrameCarrier.ofFrame (E := FrameVec) (bitsOf payload.val)] ∧
            SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
              (E := FrameVec) m2 [] ⦄ ⦄ :=
  send_deliver_extracted (ring_buffer.sim frameDefault frameClone cloneVecU8_isId)
    ring_buffer.rel_functional c m payload hR hInv hw

/-- `deliver_spec_extracted` at the extracted ring buffer. `[EXTRACTED: aeneas + bridge]` -/
theorem deliver_spec_extracted_RB
    (c : stuffed_channel.StuffedChannel (ring_buffer.RingBuffer FrameVec)) (m : SChanRB)
    (p : Frame) (ps : List Frame) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := FrameVec) m (p :: ps)) :
    stuffed_channel.StuffedChannel.deliver rbRecord c ⦃ r c' =>
      ∃ v, ∃ m' : SChanRB, r = .Ok v ∧ bitsOf v.val = p ∧ SChanRel c' m' ∧
        QueueModel.toList (α := FrameVec) m'.out =
          QueueModel.toList (α := FrameVec) m.out ++ [FrameCarrier.ofFrame (E := FrameVec) p] ∧
        SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := FrameVec) m' ps ⦄ :=
  deliver_spec_extracted (ring_buffer.sim frameDefault frameClone cloneVecU8_isId)
    ring_buffer.rel_functional c m p ps hR hInv

/-- The headline chain from the Rust constructor, at the ring buffer: `StuffedChannel::new(cap)`,
then a successful `send(payload)`, then `deliver()` returns `Ok(v)` with exactly the payload's bytes,
and `queued()` is then 1. The only hypothesis bounds the payload well below `usize::MAX`.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_from_new_RB (cap : Std.Usize) (payload : Slice Std.U8)
    (hw : 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannelRingBufferVecU8.new cap ⦃ c =>
      stuffed_channel.StuffedChannel.send rbRecord c payload ⦃ r c1 =>
        r = .Ok () →
          stuffed_channel.StuffedChannel.deliver rbRecord c1 ⦃ r2 c2 =>
            ∃ v, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧
              stuffed_channel.StuffedChannel.queued rbRecord c2 ⦃ n => n.val = 1 ⦄ ⦄ ⦄ ⦄ := by
  apply WP.spec_mono (new_idle_RB cap)
  rintro c ⟨m, hR, hInv, hl⟩
  have hc0 : c.wire.val.length = 0 := by
    have h1 := hR.2.1
    rw [hInv.1] at h1
    simpa [bytesOf] using h1
  apply WP.spec_mono (send_deliver_extracted_RB c m payload hR hInv (by omega))
  rintro ⟨r, c1⟩ h hr
  apply WP.spec_mono (h hr)
  rintro ⟨r2, c2⟩ ⟨v, m2, hr2, hv, hR2, hl2, -⟩
  refine ⟨v, hr2, hv, ?_⟩
  apply WP.spec_mono (queued_agrees (ring_buffer.sim frameDefault frameClone cloneVecU8_isId)
    ring_buffer.rel_functional c2 m2 hR2)
  intro n hn
  rw [hn, hl2, hl]
  simp

/-- `send_deliver_extracted` at the extracted `VecQueue`, by the same proof: no hypothesis on the
queue remains. `[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_extracted_VQ (c : stuffed_channel.StuffedChannel (queue.VecQueue FrameVec))
    (m : SChanVQ) (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := FrameVec) m [])
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send vqRecord c payload ⦃ r c1 =>
      r = .Ok () →
        stuffed_channel.StuffedChannel.deliver vqRecord c1 ⦃ r2 c2 =>
          ∃ v, ∃ m2 : SChanVQ, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧ SChanRel c2 m2 ∧
            QueueModel.toList (α := FrameVec) m2.out =
              QueueModel.toList (α := FrameVec) m.out ++
                [FrameCarrier.ofFrame (E := FrameVec) (bitsOf payload.val)] ∧
            SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
              (E := FrameVec) m2 [] ⦄ ⦄ :=
  send_deliver_extracted (vec_queue.sim frameClone) vec_queue.rel_functional c m payload hR hInv hw

/-- `deliver_spec_extracted` at the extracted `VecQueue`. `[EXTRACTED: aeneas + bridge]` -/
theorem deliver_spec_extracted_VQ (c : stuffed_channel.StuffedChannel (queue.VecQueue FrameVec))
    (m : SChanVQ) (p : Frame) (ps : List Frame) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := FrameVec) m (p :: ps)) :
    stuffed_channel.StuffedChannel.deliver vqRecord c ⦃ r c' =>
      ∃ v, ∃ m' : SChanVQ, r = .Ok v ∧ bitsOf v.val = p ∧ SChanRel c' m' ∧
        QueueModel.toList (α := FrameVec) m'.out =
          QueueModel.toList (α := FrameVec) m.out ++ [FrameCarrier.ofFrame (E := FrameVec) p] ∧
        SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := FrameVec) m' ps ⦄ :=
  deliver_spec_extracted (vec_queue.sim frameClone) vec_queue.rel_functional c m p ps hR hInv

/-- The same headline chain from `StuffedChannel::with_queue(cap)` at the `VecQueue` record.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_from_new_VQ (cap : Std.Usize) (payload : Slice Std.U8)
    (hw : 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.with_queue vqRecord cap ⦃ c =>
      stuffed_channel.StuffedChannel.send vqRecord c payload ⦃ r c1 =>
        r = .Ok () →
          stuffed_channel.StuffedChannel.deliver vqRecord c1 ⦃ r2 c2 =>
            ∃ v, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧
              stuffed_channel.StuffedChannel.queued vqRecord c2 ⦃ n => n.val = 1 ⦄ ⦄ ⦄ ⦄ := by
  apply WP.spec_mono (with_queue_idle_VQ cap)
  rintro c ⟨m, hR, hInv, hl⟩
  have hc0 : c.wire.val.length = 0 := by
    have h1 := hR.2.1
    rw [hInv.1] at h1
    simpa [bytesOf] using h1
  apply WP.spec_mono (send_deliver_extracted_VQ c m payload hR hInv (by omega))
  rintro ⟨r, c1⟩ h hr
  apply WP.spec_mono (h hr)
  rintro ⟨r2, c2⟩ ⟨v, m2, hr2, hv, hR2, hl2, -⟩
  refine ⟨v, hr2, hv, ?_⟩
  apply WP.spec_mono (queued_agrees (vec_queue.sim frameClone) vec_queue.rel_functional c2 m2 hR2)
  intro n hn
  rw [hn, hl2, hl]
  simp

end FramedChannel.Bridge.stuffed_channel

#print axioms FramedChannel.Bridge.stuffed_channel.with_queue_idle
#print axioms FramedChannel.Bridge.stuffed_channel.new_idle_RB
#print axioms FramedChannel.Bridge.stuffed_channel.with_queue_idle_VQ
#print axioms FramedChannel.Bridge.stuffed_channel.send_deliver_extracted_RB
#print axioms FramedChannel.Bridge.stuffed_channel.deliver_spec_extracted_RB
#print axioms FramedChannel.Bridge.stuffed_channel.send_deliver_from_new_RB
#print axioms FramedChannel.Bridge.stuffed_channel.send_deliver_extracted_VQ
#print axioms FramedChannel.Bridge.stuffed_channel.deliver_spec_extracted_VQ
#print axioms FramedChannel.Bridge.stuffed_channel.send_deliver_from_new_VQ
