-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Channel.Composite
import FramedChannelAeneas.Bridge.RingBuffer.Instance
import FramedChannelAeneas.Bridge.VecQueue.Instance

/-!
# Bridge/Channel/Instance: substitution `Channel[RB/VQ]` on the extracted code

`[EXTRACTED: aeneas + bridge]` -- the channel theorems of `Composite.lean`, proved once
over any lawful extracted queue record, instantiated at the two extracted queues with no reproof.

* the ring buffer: `rbRecord`, the record `channel.ChannelRingBufferVecU8.new` builds, with the
  simulation `sim` at the derived `Clone` of `Vec<u8>`, whose `CloneIsId` is *proved*
  (`cloneVecU8_isId`), and `Default` for `Vec<u8>`, which needs no hypothesis;
* `VecQueue`: `vqRecord`, with `sim`, which needs no trait hypothesis at all. No
  `rust/src` code builds a `VecQueue` channel; the instantiation happens here, as it does in
  `rust/tests`.

The instantiated theorems carry no `QueueSim`, `CloneIsId` or `Default` hypothesis. The headline
chain `send_deliver_from_new_RB`/`_VQ` starts at the Rust constructors (`Channel::new`,
`Channel::with_queue`), through each queue's `with_capacity_rel`, so no idle state is assumed.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Chan FrameCarrier FrameOK ChanInv encodeFrame parseFrame)

section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hfun

/-- `Channel::with_queue` over any record whose `with_capacity` returns a state related to an empty
model queue: the new channel is related to an idle specification channel. -/
theorem with_queue_idle
    (hwc : ∀ cap, inst.with_capacity cap ⦃ s => ∃ q, R s q ∧ QueueModel.toList (Q := Q) (α := alloc.vec.Vec Std.U8) q = [] ⦄)
    (cap : Std.Usize) :
    channel.Channel.with_queue inst cap ⦃ c => ∃ m : Chan (ExtQ S Q inst R), ChanRel c m ∧
      ChanInv (E := alloc.vec.Vec Std.U8) m [] ∧
      QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out = [] ⦄ := by
  unfold channel.Channel.with_queue
  step with hwc cap as ⟨q, s, hq, hl⟩
  have hl' := extToList_eq (T := alloc.vec.Vec Std.U8) (inst := inst) hfun ⟨s, q, hq⟩ q hq
  refine ⟨{ out := ⟨s, q, hq⟩, wire := [], inFlight := 0 }, ⟨rfl, ?_, ?_⟩, ⟨rfl, rfl, by simp, ?_⟩, ?_⟩
  · simp [bitsOf]
  · simp
  · simp only [hl', hl, List.length_nil, Nat.add_zero, Nat.zero_le]
  · rw [hl', hl]
end

/-- `Channel::new` (the ring buffer channel) starts idle: related to a specification channel with
no pending frame and an empty queue, at every capacity. `[EXTRACTED: aeneas + bridge]` -/
theorem new_idle_RB (cap : Std.Usize) :
    channel.ChannelRingBufferVecU8.new cap ⦃ c => ∃ m : ChanRB, ChanRel c m ∧
      ChanInv (E := FrameVec) m [] ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := by
  unfold channel.ChannelRingBufferVecU8.new
  apply with_queue_idle ring_buffer.rel_functional
  intro cap
  apply WP.spec_mono (ring_buffer.with_capacity_rel frameDefault frameClone cloneVecU8_isId
    (alloc.vec.Vec.new Std.U8) rfl cap)
  rintro s ⟨hinv, hlen, -⟩
  refine ⟨⟨ring_buffer.toModel s, hinv⟩, rfl, ?_⟩
  show FramedChannel.RingBuffer.contents (ring_buffer.toModel s) = []
  simp [FramedChannel.RingBuffer.contents, hlen]

/-- `Channel::with_queue` at the `VecQueue` record starts idle. `[EXTRACTED: aeneas + bridge]` -/
theorem with_queue_idle_VQ (cap : Std.Usize) :
    channel.Channel.with_queue vqRecord cap ⦃ c => ∃ m : ChanVQ, ChanRel c m ∧
      ChanInv (E := FrameVec) m [] ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := by
  apply with_queue_idle vec_queue.rel_functional
  intro cap
  apply WP.spec_mono (vec_queue.with_capacity_rel frameClone cap)
  intro s hs
  exact ⟨_, hs, rfl⟩

/-- `send_deliver_extracted` at the extracted ring buffer: no simulation, `CloneIsId` or `Default`
hypothesis remains. `[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_extracted_RB (c : channel.Channel (ring_buffer.RingBuffer FrameVec)) (m : ChanRB)
    (payload : Slice Std.U8) (hR : ChanRel c m) (hInv : ChanInv (E := FrameVec) m [])
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send rbRecord c payload ⦃ r c1 =>
      r = .Ok () →
        channel.Channel.deliver rbRecord c1 ⦃ r2 c2 =>
          ∃ v, ∃ m2 : ChanRB, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧ ChanRel c2 m2 ∧
            QueueModel.toList (α := FrameVec) m2.out =
              QueueModel.toList (α := FrameVec) m.out ++
                [FrameCarrier.ofFrame (E := FrameVec) (bitsOf payload.val)] ∧
            ChanInv (E := FrameVec) m2 [] ⦄ ⦄ :=
  send_deliver_extracted (ring_buffer.sim frameDefault frameClone cloneVecU8_isId) ring_buffer.rel_functional c m payload hR hInv hw

/-- `deliver_spec_extracted` at the extracted ring buffer. `[EXTRACTED: aeneas + bridge]` -/
theorem deliver_spec_extracted_RB (c : channel.Channel (ring_buffer.RingBuffer FrameVec)) (m : ChanRB)
    (p : FramedChannel.Channel.Frame) (ps : List FramedChannel.Channel.Frame)
    (hR : ChanRel c m) (hInv : ChanInv (E := FrameVec) m (p :: ps)) :
    channel.Channel.deliver rbRecord c ⦃ r c' =>
      ∃ v, ∃ m' : ChanRB, r = .Ok v ∧ bitsOf v.val = p ∧ ChanRel c' m' ∧
        QueueModel.toList (α := FrameVec) m'.out =
          QueueModel.toList (α := FrameVec) m.out ++ [FrameCarrier.ofFrame (E := FrameVec) p] ∧
        ChanInv (E := FrameVec) m' ps ⦄ :=
  deliver_spec_extracted (ring_buffer.sim frameDefault frameClone cloneVecU8_isId) ring_buffer.rel_functional c m p ps hR hInv

/-- The headline chain from the Rust constructor, at the ring buffer: `Channel::new(cap)`, then a
successful `send(payload)`, then `deliver()` returns `Ok(v)` with exactly the payload's bytes, and
`queued()` is then 1. The only hypothesis is that the payload is not within seven bytes of
`usize::MAX`. `[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_from_new_RB (cap : Std.Usize) (payload : Slice Std.U8)
    (hw : payload.val.length + 7 ≤ Usize.max) :
    channel.ChannelRingBufferVecU8.new cap ⦃ c =>
      channel.Channel.send rbRecord c payload ⦃ r c1 =>
        r = .Ok () →
          channel.Channel.deliver rbRecord c1 ⦃ r2 c2 =>
            ∃ v, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧
              channel.Channel.queued rbRecord c2 ⦃ n => n.val = 1 ⦄ ⦄ ⦄ ⦄ := by
  apply WP.spec_mono (new_idle_RB cap)
  rintro c ⟨m, hR, hInv, hl⟩
  have hc0 : c.wire.val.length = 0 := by
    have h1 := hR.2.1
    rw [hInv.1] at h1
    simpa [bitsOf] using h1
  apply WP.spec_mono (send_deliver_extracted_RB c m payload hR hInv (by omega))
  rintro ⟨r, c1⟩ h hr
  apply WP.spec_mono (h hr)
  rintro ⟨r2, c2⟩ ⟨v, m2, hr2, hv, hR2, hl2, -⟩
  refine ⟨v, hr2, hv, ?_⟩
  apply WP.spec_mono (queued_agrees (ring_buffer.sim frameDefault frameClone cloneVecU8_isId) ring_buffer.rel_functional c2 m2 hR2)
  intro n hn
  rw [hn, hl2, hl]
  simp

/-- `send_deliver_extracted` at the extracted `VecQueue`, by the same proof: no hypothesis on the
queue remains. `[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_extracted_VQ (c : channel.Channel (queue.VecQueue FrameVec)) (m : ChanVQ)
    (payload : Slice Std.U8) (hR : ChanRel c m) (hInv : ChanInv (E := FrameVec) m [])
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send vqRecord c payload ⦃ r c1 =>
      r = .Ok () →
        channel.Channel.deliver vqRecord c1 ⦃ r2 c2 =>
          ∃ v, ∃ m2 : ChanVQ, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧ ChanRel c2 m2 ∧
            QueueModel.toList (α := FrameVec) m2.out =
              QueueModel.toList (α := FrameVec) m.out ++
                [FrameCarrier.ofFrame (E := FrameVec) (bitsOf payload.val)] ∧
            ChanInv (E := FrameVec) m2 [] ⦄ ⦄ :=
  send_deliver_extracted (vec_queue.sim frameClone) vec_queue.rel_functional c m payload hR hInv hw

/-- `deliver_spec_extracted` at the extracted `VecQueue`. `[EXTRACTED: aeneas + bridge]` -/
theorem deliver_spec_extracted_VQ (c : channel.Channel (queue.VecQueue FrameVec)) (m : ChanVQ)
    (p : FramedChannel.Channel.Frame) (ps : List FramedChannel.Channel.Frame)
    (hR : ChanRel c m) (hInv : ChanInv (E := FrameVec) m (p :: ps)) :
    channel.Channel.deliver vqRecord c ⦃ r c' =>
      ∃ v, ∃ m' : ChanVQ, r = .Ok v ∧ bitsOf v.val = p ∧ ChanRel c' m' ∧
        QueueModel.toList (α := FrameVec) m'.out =
          QueueModel.toList (α := FrameVec) m.out ++ [FrameCarrier.ofFrame (E := FrameVec) p] ∧
        ChanInv (E := FrameVec) m' ps ⦄ :=
  deliver_spec_extracted (vec_queue.sim frameClone) vec_queue.rel_functional c m p ps hR hInv

/-- The same headline chain from `Channel::with_queue(cap)` at the `VecQueue` record.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_from_new_VQ (cap : Std.Usize) (payload : Slice Std.U8)
    (hw : payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.with_queue vqRecord cap ⦃ c =>
      channel.Channel.send vqRecord c payload ⦃ r c1 =>
        r = .Ok () →
          channel.Channel.deliver vqRecord c1 ⦃ r2 c2 =>
            ∃ v, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧
              channel.Channel.queued vqRecord c2 ⦃ n => n.val = 1 ⦄ ⦄ ⦄ ⦄ := by
  apply WP.spec_mono (with_queue_idle_VQ cap)
  rintro c ⟨m, hR, hInv, hl⟩
  have hc0 : c.wire.val.length = 0 := by
    have h1 := hR.2.1
    rw [hInv.1] at h1
    simpa [bitsOf] using h1
  apply WP.spec_mono (send_deliver_extracted_VQ c m payload hR hInv (by omega))
  rintro ⟨r, c1⟩ h hr
  apply WP.spec_mono (h hr)
  rintro ⟨r2, c2⟩ ⟨v, m2, hr2, hv, hR2, hl2, -⟩
  refine ⟨v, hr2, hv, ?_⟩
  apply WP.spec_mono (queued_agrees (vec_queue.sim frameClone) vec_queue.rel_functional c2 m2 hR2)
  intro n hn
  rw [hn, hl2, hl]
  simp

end FramedChannel.Bridge.channel

#print axioms FramedChannel.Bridge.channel.with_queue_idle
#print axioms FramedChannel.Bridge.channel.new_idle_RB
#print axioms FramedChannel.Bridge.channel.with_queue_idle_VQ
#print axioms FramedChannel.Bridge.channel.send_deliver_extracted_RB
#print axioms FramedChannel.Bridge.channel.deliver_spec_extracted_RB
#print axioms FramedChannel.Bridge.channel.send_deliver_from_new_RB
#print axioms FramedChannel.Bridge.channel.send_deliver_extracted_VQ
#print axioms FramedChannel.Bridge.channel.deliver_spec_extracted_VQ
#print axioms FramedChannel.Bridge.channel.send_deliver_from_new_VQ
