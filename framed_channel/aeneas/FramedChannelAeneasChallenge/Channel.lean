-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Channel.Defs

/-!
# FramedChannelAeneasChallenge.Channel: approved statements (extracted channel)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/Channel/{Frame,Refinement,Composite,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Frame Chan FrameCarrier FrameOK)
end FramedChannel.Bridge.channel

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (marker parseFrame encodeFrame lenBytes)

/-- Frame encoder refinement: the extracted `encode_frame` appends exactly the specification's
frame of the payload (marker, varint length, payload, bitwise CRC-8) to the output, and never
fails, given `len` equal to the payload length and room for the frame. -/
theorem encode_frame_refines (payload : Slice Std.U8) (len : Std.U32) (out : alloc.vec.Vec Std.U8)
    (hlen : len.val = payload.val.length)
    (hw : out.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.encode_frame payload len out
      ⦃ v => bitsOf v.val = bitsOf out.val ++ FramedChannel.Channel.encodeFrame (bitsOf payload.val) ⦄ := sorry

/-- Frame parser refinement: the extracted `parse_frame` never fails, and its result is related to
the specification's `parseFrame` of the same bytes by `ParsePost`. The varint length and the CRC-8
are reached only through `decode_refines` and `crc8_refines`. -/
theorem parse_frame_refines (wire : Slice Std.U8) :
    WP.spec (channel.parse_frame wire) (ParsePost (bitsOf wire.val)) := sorry

/-- The extracted frame round trip: on any wire that starts with the specification's encoding of a
payload `p` whose length fits a `u32`, the extracted parser returns exactly `p` and consumes exactly
the frame. The only hypothesis is the length bound (`send` refuses longer payloads). The
declared-length divergence of `ParsePost` cannot arise, because the declared length is `p.length`.
-/
theorem parse_frame_encode_frame_extracted (w : Slice Std.U8) (p rest : List (BitVec 8))
    (hp : p.length ≤ U32.max) (hw : bitsOf w.val = FramedChannel.Channel.encodeFrame p ++ rest) :
    channel.parse_frame w
      ⦃ o => ∃ v used, o = some (v, used) ∧ bitsOf v.val = p ∧
        used.val = (FramedChannel.Channel.encodeFrame p).length ⦄ := sorry

/-- The marker-byte frame, at the extracted parser: a payload of exactly 126 bytes has `0x7E` (the
frame marker) as its single varint length byte, so its frame starts with two marker bytes. The
extracted `parse_frame` still returns exactly that payload and consumes all 129 bytes: it reads the
second marker as a length, not as a frame boundary. -/
theorem parse_frame_len126_extracted (w : Slice Std.U8) (p rest : List (BitVec 8))
    (hp : p.length = 126) (hw : bitsOf w.val = FramedChannel.Channel.encodeFrame p ++ rest) :
    (FramedChannel.Channel.encodeFrame p).take 2 =
        [FramedChannel.Channel.marker, FramedChannel.Channel.marker] ∧
      channel.parse_frame w
        ⦃ o => ∃ v used, o = some (v, used) ∧ bitsOf v.val = p ∧ used.val = 129 ⦄ := sorry
end FramedChannel.Bridge.channel

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Chan FrameCarrier FrameOK encodeFrame parseFrame)
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
  capacity compare, and Aeneas models that add's overflow as a panic (a debug build's behavior;
  a release build wraps). Every composite theorem discharges it from `ChanInv`, whose fourth
  conjunct bounds the sum by the capacity, itself a `usize`.
* `hw`: room on the wire for the frame. Aeneas bounds a `Vec` by `Usize.max` and panics beyond it
  (real Rust panics earlier, at `isize::MAX` bytes). It excludes only payloads within seven bytes of
  that bound. -/
theorem send_refines (c : channel.Channel S) (m : Chan (Ext S Q (alloc.vec.Vec Std.U8) inst R))
    (payload : Slice Std.U8) (hR : ChanRel c m)
    (hovf : (QueueModel.toList (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R) (α := alloc.vec.Vec Std.U8) m.out).length +
      m.inFlight ≤ Usize.max)
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r c' =>
      (∀ m', FramedChannel.Channel.send (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) = .ok m' →
        r = .Ok () ∧ ChanRel c' m') ∧
      (FramedChannel.Channel.send (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) = .fail →
        r = .Err () ∧ c' = c) ⦄ := sorry

omit hfun in
/-- Take refinement: the extracted `take` pops exactly what the specification's queue pops, and
returns `None` with the channel unchanged exactly when the specification's pop fails. -/
theorem take_refines (c : channel.Channel S) (m : Chan (Ext S Q (alloc.vec.Vec Std.U8) inst R))
    (hR : ChanRel c m) :
    channel.Channel.take inst c ⦃ o c' =>
      match QueueModel.pop (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R) (α := alloc.vec.Vec Std.U8) m.out with
      | .ok (y, q') => o = some y ∧ ChanRel c' { m with out := q' }
      | .fail => o = none ∧ c' = c ⦄ := sorry

/-- `queued` is the length of the specification queue's contents. -/
theorem queued_agrees (c : channel.Channel S) (m : Chan (Ext S Q (alloc.vec.Vec Std.U8) inst R))
    (hR : ChanRel c m) :
    channel.Channel.queued inst c ⦃ n =>
      n.val = (QueueModel.toList (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R) (α := alloc.vec.Vec Std.U8) m.out).length ⦄ := sorry

omit hfun in
/-- Deliver refinement, over any lawful extracted queue record. When the specification's `deliver`
succeeds, the extracted `deliver` returns `Ok v` where `v` reads as exactly the frame the
specification parsed, and the channels are related again, **or** the wire's head frame declares a
length of `2 ^ 32` or more (`DeclaresWideLength`, the parser divergence). When the specification's
`deliver` fails, the extracted one returns `Err` with the channel unchanged. No hypothesis: the
pushed element is `v` itself (`cloneVecU8_isId`), which is the carrier of the parsed frame
(`ofFrame_bitsOf`). -/
theorem deliver_refines (c : channel.Channel S) (m : Chan (Ext S Q (alloc.vec.Vec Std.U8) inst R))
    (hR : ChanRel c m) :
    channel.Channel.deliver inst c ⦃ r c' =>
      (∀ m', FramedChannel.Channel.deliver (E := alloc.vec.Vec Std.U8) m = .ok m' →
        (∃ v p rest, r = .Ok v ∧ parseFrame m.wire = .ok (p, rest) ∧ bitsOf v.val = p ∧ ChanRel c' m') ∨
        DeclaresWideLength m.wire) ∧
      (FramedChannel.Channel.deliver (E := alloc.vec.Vec Std.U8) m = .fail → r = .Err () ∧ c' = c) ⦄ := sorry
end
end FramedChannel.Bridge.channel

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Chan FrameCarrier FrameOK ChanInv encodeFrame parseFrame)
section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)] [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hsim hfun

/-- `deliver_spec` at the extracted code: delivering the oldest pending frame returns it as `Ok v`,
pushes exactly its carrier onto the specification queue, and keeps the invariant. The parser
divergence is excluded by `ChanInv` (every pending frame is `FrameOK`). -/
theorem deliver_spec_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (p : FramedChannel.Channel.Frame) (ps : List FramedChannel.Channel.Frame)
    (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m (p :: ps)) :
    channel.Channel.deliver inst c ⦃ r c' =>
      ∃ v m', r = .Ok v ∧ bitsOf v.val = p ∧ ChanRel c' m' ∧
        QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out =
          QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out ++
            [FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) p] ∧
        ChanInv (E := alloc.vec.Vec Std.U8) m' ps ⦄ := sorry

/-- `send_inv` at the extracted code: a successful extracted `send` keeps the invariant with the
payload appended to the pending frames; a refusal leaves the channel unchanged. -/
theorem send_inv_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (ps : List FramedChannel.Channel.Frame) (payload : Slice Std.U8)
    (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m ps)
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r c' =>
      (r = .Ok () → ∃ m' : Chan (ExtQ S Q inst R), ChanRel c' m' ∧ ChanInv (E := alloc.vec.Vec Std.U8) m' (ps ++ [bitsOf payload.val])) ∧
      (r = .Err () → c' = c) ⦄ := sorry

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] in
/-- `send_bounded` at the extracted code: after a successful extracted `send`, queued plus in-flight
is within the capacity, with no invariant assumed (only `send_refines`' overflow and wire-room
hypotheses). -/
theorem send_bounded_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (payload : Slice Std.U8) (hR : ChanRel c m)
    (hovf : (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out).length +
      m.inFlight ≤ Usize.max)
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r c' =>
      r = .Ok () → ∃ m', ChanRel c' m' ∧
        (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out).length + m'.inFlight ≤
          QueueModel.capacity (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out ⦄ := sorry

/-- The headline composite at the extracted code: from an extracted channel related to an idle
specification channel, a successful extracted `send` followed by an extracted `deliver` returns
`Ok v` whose bytes are exactly the payload's, the related specification queue grows by exactly that
frame, and the channel is idle again. The one hypothesis beyond the relation is room on the wire.
Proved from the component laws alone, through the core `send_deliver`'s ingredients. -/
theorem send_deliver_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (payload : Slice Std.U8) (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m [])
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r c1 =>
      r = .Ok () →
        channel.Channel.deliver inst c1 ⦃ r2 c2 =>
          ∃ v m2, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧ ChanRel c2 m2 ∧
            QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m2.out =
              QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out ++
                [FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) (bitsOf payload.val)] ∧
            ChanInv (E := alloc.vec.Vec Std.U8) m2 [] ⦄ ⦄ := sorry

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] in
/-- `send_refuses_too_long` at the extracted code: a payload longer than `u32::MAX` bytes is refused
with the channel unchanged, whatever the queue holds. No wire-room hypothesis: the refusal happens
before the frame is written. (Such a payload exists only where `usize` is 64 bits; the statement is
uniform.) -/
theorem send_refuses_too_long_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (ps : List FramedChannel.Channel.Frame) (payload : Slice Std.U8)
    (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m ps)
    (hlong : U32.max < payload.val.length) :
    channel.Channel.send inst c payload ⦃ r c' => r = .Err () ∧ c' = c ⦄ := sorry

/-- `send_discharges_not_full` at the extracted code: when the extracted `send` succeeds, the
extracted queue record's own `is_full` reports `false` on the queue it saw. -/
theorem send_discharges_not_full_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (ps : List FramedChannel.Channel.Frame) (payload : Slice Std.U8)
    (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m ps)
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r _ =>
      r = .Ok () → inst.is_full c.out ⦃ b => b = false ⦄ ⦄ := sorry
end
end FramedChannel.Bridge.channel

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
end

/-- `Channel::new` (the ring buffer channel) starts idle: related to a specification channel with
no pending frame and an empty queue, at every capacity. -/
theorem new_idle_RB (cap : Std.Usize) :
    channel.ChannelRingBufferVecU8.new cap ⦃ c => ∃ m : ChanRB, ChanRel c m ∧
      ChanInv (E := FrameVec) m [] ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := sorry

/-- `Channel::with_queue` at the `VecQueue` record starts idle. -/
theorem with_queue_idle_VQ (cap : Std.Usize) :
    channel.Channel.with_queue vqRecord cap ⦃ c => ∃ m : ChanVQ, ChanRel c m ∧
      ChanInv (E := FrameVec) m [] ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := sorry

/-- `send_deliver_extracted` at the extracted ring buffer: no simulation, `CloneIsId` or `Default`
hypothesis remains. -/
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
            ChanInv (E := FrameVec) m2 [] ⦄ ⦄ := sorry

/-- `deliver_spec_extracted` at the extracted ring buffer. -/
theorem deliver_spec_extracted_RB (c : channel.Channel (ring_buffer.RingBuffer FrameVec)) (m : ChanRB)
    (p : FramedChannel.Channel.Frame) (ps : List FramedChannel.Channel.Frame)
    (hR : ChanRel c m) (hInv : ChanInv (E := FrameVec) m (p :: ps)) :
    channel.Channel.deliver rbRecord c ⦃ r c' =>
      ∃ v, ∃ m' : ChanRB, r = .Ok v ∧ bitsOf v.val = p ∧ ChanRel c' m' ∧
        QueueModel.toList (α := FrameVec) m'.out =
          QueueModel.toList (α := FrameVec) m.out ++ [FrameCarrier.ofFrame (E := FrameVec) p] ∧
        ChanInv (E := FrameVec) m' ps ⦄ := sorry

/-- The headline chain from the Rust constructor, at the ring buffer: `Channel::new(cap)`, then a
successful `send(payload)`, then `deliver()` returns `Ok(v)` with exactly the payload's bytes, and
`queued()` is then 1. The only hypothesis is that the payload is not within seven bytes of
`usize::MAX`. -/
theorem send_deliver_from_new_RB (cap : Std.Usize) (payload : Slice Std.U8)
    (hw : payload.val.length + 7 ≤ Usize.max) :
    channel.ChannelRingBufferVecU8.new cap ⦃ c =>
      channel.Channel.send rbRecord c payload ⦃ r c1 =>
        r = .Ok () →
          channel.Channel.deliver rbRecord c1 ⦃ r2 c2 =>
            ∃ v, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧
              channel.Channel.queued rbRecord c2 ⦃ n => n.val = 1 ⦄ ⦄ ⦄ ⦄ := sorry

/-- `send_deliver_extracted` at the extracted `VecQueue`, by the same proof: no hypothesis on the
queue remains. -/
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
            ChanInv (E := FrameVec) m2 [] ⦄ ⦄ := sorry

/-- `deliver_spec_extracted` at the extracted `VecQueue`. -/
theorem deliver_spec_extracted_VQ (c : channel.Channel (queue.VecQueue FrameVec)) (m : ChanVQ)
    (p : FramedChannel.Channel.Frame) (ps : List FramedChannel.Channel.Frame)
    (hR : ChanRel c m) (hInv : ChanInv (E := FrameVec) m (p :: ps)) :
    channel.Channel.deliver vqRecord c ⦃ r c' =>
      ∃ v, ∃ m' : ChanVQ, r = .Ok v ∧ bitsOf v.val = p ∧ ChanRel c' m' ∧
        QueueModel.toList (α := FrameVec) m'.out =
          QueueModel.toList (α := FrameVec) m.out ++ [FrameCarrier.ofFrame (E := FrameVec) p] ∧
        ChanInv (E := FrameVec) m' ps ⦄ := sorry

/-- The same headline chain from `Channel::with_queue(cap)` at the `VecQueue` record. -/
theorem send_deliver_from_new_VQ (cap : Std.Usize) (payload : Slice Std.U8)
    (hw : payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.with_queue vqRecord cap ⦃ c =>
      channel.Channel.send vqRecord c payload ⦃ r c1 =>
        r = .Ok () →
          channel.Channel.deliver vqRecord c1 ⦃ r2 c2 =>
            ∃ v, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧
              channel.Channel.queued vqRecord c2 ⦃ n => n.val = 1 ⦄ ⦄ ⦄ ⦄ := sorry
end FramedChannel.Bridge.channel
