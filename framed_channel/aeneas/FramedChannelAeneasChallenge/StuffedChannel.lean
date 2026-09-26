-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.StuffedChannel.Defs

/-!
# FramedChannelAeneasChallenge.StuffedChannel: approved statements (extracted transparent channel)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/StuffedChannel/{Frame,Refinement,Composite,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Byte Frame FrameOK lenBytes)
open FramedChannel.StuffedChannel (body encodeStuffed parseStuffed)

/-- Body refinement: the extracted `body` returns exactly the specification's frame body (varint
length, payload, bitwise CRC-8) and never fails, given `len` equal to the payload length and room
for the body. `[EXTRACTED: aeneas + bridge]` -/
theorem body_refines (payload : Slice Std.U8) (len : Std.U32)
    (hlen : len.val = payload.val.length)
    (hroom : payload.val.length + 6 ≤ Usize.max) :
    stuffed_channel.body payload len
      ⦃ v => bytesOf v.val = body (K := FramedChannel.Crc8.Bitwise) (bitsOf payload.val) ⦄ := sorry

/-- Framing refinement: the extracted `encode_stuffed` appends exactly the specification's stuffed
frame -- the body, byte-stuffed and terminated by the flag -- to the output, and never fails, given
`len` equal to the payload length and room for the frame. `[EXTRACTED: aeneas + bridge]` -/
theorem encode_stuffed_refines (payload : Slice Std.U8) (len : Std.U32)
    (out : alloc.vec.Vec Std.U8) (hlen : len.val = payload.val.length)
    (hroom : out.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.encode_stuffed payload len out
      ⦃ v => bytesOf v.val
        = bytesOf out.val ++ encodeStuffed (C := FramedChannel.Stuff.Hdlc)
            (K := FramedChannel.Crc8.Bitwise) (bitsOf payload.val) ⦄ := sorry

/-- Parser refinement: the extracted `parse_stuffed` never fails, and its result is related to the
specification's `parseStuffed` of the same bytes by `ParsePost`. The stuffing, the varint length and
the CRC-8 are reached only through `unstuff_refines`, `decode_refines` and `crc8_refines`; no loop of
any of the three is unfolded here. `[EXTRACTED: aeneas + bridge]` -/
theorem parse_stuffed_refines (wire : Slice Std.U8) :
    WP.spec (stuffed_channel.parse_stuffed wire) (ParsePost (bytesOf wire.val)) := sorry

/-- The extracted stuffed round trip: on any wire that starts with the specification's stuffed
encoding of a payload `p` whose length fits a `u32`, the extracted parser returns exactly `p` and
consumes exactly the frame. The only hypothesis is the length bound (`send` refuses longer
payloads). `[EXTRACTED: aeneas + bridge]` -/
theorem parse_stuffed_encode_stuffed_extracted (w : Slice Std.U8) (p : Frame) (rest : List Nat)
    (hp : p.length ≤ U32.max)
    (hw : bytesOf w.val = encodeStuffed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) p ++ rest) :
    stuffed_channel.parse_stuffed w
      ⦃ o => ∃ v used, o = some (v, used) ∧ bitsOf v.val = p ∧
        used.val = (encodeStuffed (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) p).length ⦄ := sorry
end FramedChannel.Bridge.stuffed_channel

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Bridge.channel (ExtQ)
open FramedChannel.Channel (Frame FrameCarrier FrameOK)
open FramedChannel.StuffedChannel (SChan SChanInv encodeStuffed parseStuffed)

/-- TRANSPARENCY at the extracted code: the bytes the extracted `encode_stuffed` appends to the wire
carry the HDLC flag nowhere but at their last position, so a receiver may scan to the next flag.
This is the claim the unstuffed `channel.encode_frame` cannot make --
`lean/FramedChannel/Evidence/Countermodels.lean` refutes the corresponding statement about it in the
kernel. `[EXTRACTED: aeneas + bridge]` -/
theorem wire_flag_free_extracted (payload : Slice Std.U8) (len : Std.U32)
    (out : alloc.vec.Vec Std.U8) (hlen : len.val = payload.val.length)
    (hroom : out.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.encode_stuffed payload len out ⦃ v =>
      ∃ w, bytesOf v.val = bytesOf out.val ++ w ∧
        (∀ b ∈ w.dropLast, b ≠ FramedChannel.Stuff.marker) ∧
        w.getLast? = some FramedChannel.Stuff.marker ⦄ := sorry
end FramedChannel.Bridge.stuffed_channel

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Frame FrameCarrier FrameOK)
open FramedChannel.StuffedChannel (SChan encodeStuffed parseStuffed)
section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hsim hfun

/-- Send refinement, over any lawful extracted queue record: the extracted `send` succeeds exactly
when the specification's `send` does, and then the two channels are related again; it refuses
(`Err`, state unchanged) exactly when the specification fails.

Two hypotheses remain, and both are genuine extracted behavior rather than proof artifacts:
* `hovf`: queued plus in-flight fits a `usize`. The Rust adds `len()` and `in_flight` before the
  capacity compare, and Aeneas models that add's overflow as a panic. Every composite theorem
  discharges it from `SChanInv`, whose fourth conjunct bounds the sum by the capacity, itself a
  `usize`.
* `hw`: room on the wire for the stuffed frame. It excludes only payloads within a small constant
  factor of that bound. `[EXTRACTED: aeneas + bridge]` -/
theorem send_refines (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (payload : Slice Std.U8)
    (hR : SChanRel c m)
    (hovf : (QueueModel.toList (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
      (α := alloc.vec.Vec Std.U8) m.out).length + m.inFlight ≤ Usize.max)
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c' =>
      (∀ m', FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val)
            = .ok m' → r = .Ok () ∧ SChanRel c' m') ∧
      (FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val)
            = .fail → r = .Err () ∧ c' = c) ⦄ := sorry

omit hfun in
/-- Take refinement: the extracted `take` pops exactly what the specification's queue pops, and
returns `None` with the channel unchanged exactly when the specification's pop fails.
`[EXTRACTED: aeneas + bridge]` -/
theorem take_refines (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : SChanRel c m) :
    stuffed_channel.StuffedChannel.take inst c ⦃ o c' =>
      match QueueModel.pop (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
          (α := alloc.vec.Vec Std.U8) m.out with
      | .ok (y, q') => o = some y ∧ SChanRel c' { m with out := q' }
      | .fail => o = none ∧ c' = c ⦄ := sorry

/-- `queued` is the length of the specification queue's contents. `[EXTRACTED: aeneas + bridge]` -/
theorem queued_agrees (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : SChanRel c m) :
    stuffed_channel.StuffedChannel.queued inst c ⦃ n =>
      n.val = (QueueModel.toList (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
        (α := alloc.vec.Vec Std.U8) m.out).length ⦄ := sorry

omit hfun in
/-- Deliver refinement, over any lawful extracted queue record. When the specification's `deliver`
succeeds, the extracted `deliver` returns `Ok v` where `v` reads as exactly the frame the
specification parsed, and the channels are related again, **or** the wire's head frame declares a
length of `2 ^ 32` or more (`DeclaresWideLength`, the varint layer's divergence). When the
specification's `deliver` fails, the extracted one returns `Err` with the channel unchanged. No
hypothesis: the pushed element is `v` itself (`cloneVecU8_isId`), which is the carrier of the parsed
frame (`ofFrame_bitsOf`). `[EXTRACTED: aeneas + bridge]` -/
theorem deliver_refines (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : SChanRel c m) :
    stuffed_channel.StuffedChannel.deliver inst c ⦃ r c' =>
      (∀ m', FramedChannel.StuffedChannel.deliver (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m = .ok m' →
        (∃ v p rest, r = .Ok v ∧ parseStuffed (C := FramedChannel.Stuff.Hdlc)
            (K := FramedChannel.Crc8.Bitwise) m.wire = .ok (p, rest) ∧ bitsOf v.val = p ∧
            SChanRel c' m') ∨
        DeclaresWideLength m.wire) ∧
      (FramedChannel.StuffedChannel.deliver (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m = .fail →
        r = .Err () ∧ c' = c) ⦄ := sorry
end
end FramedChannel.Bridge.stuffed_channel

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Bridge.channel (ExtQ)
open FramedChannel.Channel (Frame FrameCarrier FrameOK)
open FramedChannel.StuffedChannel (SChan SChanInv encodeStuffed parseStuffed)
section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hsim hfun

/-- `deliver_spec` at the extracted code: delivering the oldest pending frame returns it as `Ok v`,
pushes exactly its carrier onto the specification queue, and keeps the invariant. The parser
divergence is excluded by `SChanInv` (every pending frame is `FrameOK`).
`[EXTRACTED: aeneas + bridge]` -/
theorem deliver_spec_extracted (c : stuffed_channel.StuffedChannel S) (m : SChan (ExtQ S Q inst R))
    (p : Frame) (ps : List Frame) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m (p :: ps)) :
    stuffed_channel.StuffedChannel.deliver inst c ⦃ r c' =>
      ∃ v m', r = .Ok v ∧ bitsOf v.val = p ∧ SChanRel c' m' ∧
        QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out =
          QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out ++
            [FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) p] ∧
        SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) m' ps ⦄ := sorry

/-- `send_inv` at the extracted code: a successful extracted `send` keeps the invariant with the
payload appended to the pending frames; a refusal leaves the channel unchanged.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_inv_extracted (c : stuffed_channel.StuffedChannel S) (m : SChan (ExtQ S Q inst R))
    (ps : List Frame) (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m ps)
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c' =>
      (r = .Ok () → ∃ m' : SChan (ExtQ S Q inst R), SChanRel c' m' ∧
        SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) m' (ps ++ [bitsOf payload.val])) ∧
      (r = .Err () → c' = c) ⦄ := sorry

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] in
/-- `send_bounded` at the extracted code: after a successful extracted `send`, queued plus in-flight
is within the capacity, with no invariant assumed (only `send_refines`' overflow and wire-room
hypotheses). `[EXTRACTED: aeneas + bridge]` -/
theorem send_bounded_extracted (c : stuffed_channel.StuffedChannel S) (m : SChan (ExtQ S Q inst R))
    (payload : Slice Std.U8) (hR : SChanRel c m)
    (hovf : (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out).length +
      m.inFlight ≤ Usize.max)
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c' =>
      r = .Ok () → ∃ m', SChanRel c' m' ∧
        (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out).length
            + m'.inFlight ≤
          QueueModel.capacity (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out ⦄ := sorry

/-- The headline composite at the extracted code: from an extracted channel related to an idle
specification channel, a successful extracted `send` followed by an extracted `deliver` returns
`Ok v` whose bytes are exactly the payload's, the related specification queue grows by exactly that
frame, and the channel is idle again. The one hypothesis beyond the relation is room on the wire.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_extracted (c : stuffed_channel.StuffedChannel S) (m : SChan (ExtQ S Q inst R))
    (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m [])
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c1 =>
      r = .Ok () →
        stuffed_channel.StuffedChannel.deliver inst c1 ⦃ r2 c2 =>
          ∃ v m2, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧ SChanRel c2 m2 ∧
            QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m2.out =
              QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out ++
                [FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) (bitsOf payload.val)] ∧
            SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
              (E := alloc.vec.Vec Std.U8) m2 [] ⦄ ⦄ := sorry

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] in
/-- `send_refuses_too_long` at the extracted code: a payload longer than `u32::MAX` bytes is refused
with the channel unchanged, whatever the queue holds. No wire-room hypothesis: the refusal happens
before the frame is written. `[EXTRACTED: aeneas + bridge]` -/
theorem send_refuses_too_long_extracted (c : stuffed_channel.StuffedChannel S)
    (m : SChan (ExtQ S Q inst R)) (ps : List Frame) (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m ps)
    (hlong : U32.max < payload.val.length) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c' => r = .Err () ∧ c' = c ⦄ := sorry

/-- `send_discharges_not_full` at the extracted code: when the extracted `send` succeeds, the
extracted queue record's own `is_full` reports `false` on the queue it saw.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_discharges_not_full_extracted (c : stuffed_channel.StuffedChannel S)
    (m : SChan (ExtQ S Q inst R)) (ps : List Frame) (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m ps)
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r _ =>
      r = .Ok () → inst.is_full c.out ⦃ b => b = false ⦄ ⦄ := sorry
end
end FramedChannel.Bridge.stuffed_channel

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Bridge.channel (ExtQ FrameVec frameClone frameDefault rbRecord vqRecord)
open FramedChannel.Channel (Frame FrameCarrier FrameOK)
open FramedChannel.StuffedChannel (SChan SChanInv)

/-- `StuffedChannel::new` (the ring buffer channel) starts idle: related to a specification channel
with no pending frame and an empty queue, at every capacity. `[EXTRACTED: aeneas + bridge]` -/
theorem new_idle_RB (cap : Std.Usize) :
    stuffed_channel.StuffedChannelRingBufferVecU8.new cap ⦃ c => ∃ m : SChanRB, SChanRel c m ∧
      SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) (E := FrameVec)
        m [] ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := sorry

/-- `StuffedChannel::with_queue` at the `VecQueue` record starts idle.
`[EXTRACTED: aeneas + bridge]` -/
theorem with_queue_idle_VQ (cap : Std.Usize) :
    stuffed_channel.StuffedChannel.with_queue vqRecord cap ⦃ c => ∃ m : SChanVQ, SChanRel c m ∧
      SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) (E := FrameVec)
        m [] ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := sorry

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
              (E := FrameVec) m2 [] ⦄ ⦄ := sorry

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
          (E := FrameVec) m' ps ⦄ := sorry

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
              stuffed_channel.StuffedChannel.queued rbRecord c2 ⦃ n => n.val = 1 ⦄ ⦄ ⦄ ⦄ := sorry

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
              (E := FrameVec) m2 [] ⦄ ⦄ := sorry

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
          (E := FrameVec) m' ps ⦄ := sorry

/-- The same headline chain from `StuffedChannel::with_queue(cap)` at the `VecQueue` record.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_from_new_VQ (cap : Std.Usize) (payload : Slice Std.U8)
    (hw : 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.with_queue vqRecord cap ⦃ c =>
      stuffed_channel.StuffedChannel.send vqRecord c payload ⦃ r c1 =>
        r = .Ok () →
          stuffed_channel.StuffedChannel.deliver vqRecord c1 ⦃ r2 c2 =>
            ∃ v, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧
              stuffed_channel.StuffedChannel.queued vqRecord c2 ⦃ n => n.val = 1 ⦄ ⦄ ⦄ ⦄ := sorry
end FramedChannel.Bridge.stuffed_channel
