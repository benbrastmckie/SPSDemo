-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Composition.Channel.Defs
import FramedChannel.Model.RingBuffer.Defs
import FramedChannel.Model.VecQueue.Defs

/-!
# FramedChannelChallenge.Channel: approved statements (channel composite)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Composition/Channel/Theorems.lean` and `Composition/Channel/Instances.lean`. See
`lean/FramedChannelChallenge.lean` for what a Challenge module is and what the gate checks.
-/

namespace FramedChannel.Channel
open FramedChannel

/-- Round trip of one frame under the idealized parser, composed from `varint_roundtrip`. -/
theorem parseFrame_encodeFrame (p : Frame) (rest : List Byte) (hp : p.length < 2 ^ 32) :
    parseFrame (encodeFrame p ++ rest) = .ok (p, rest) := sorry

/-- The equivalence `crc8_table ≃ crc8` entering the frame encoder. -/
theorem encodeFrameTable_eq (p : Frame) : encodeFrameTable p = encodeFrame p := sorry

/-- The capacity check of `send` discharges `push`'s not-full assumption. -/
theorem send_discharges_not_full (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c c' : Chan Q) (p : Frame) (h : send (E := E) c p = .ok c') :
    ¬ QueueModel.full (Q := Q) (α := E) c.out := sorry

/-- Bounds: after a successful `send`, queued plus in-flight is still within the capacity. This is
what the composite needs from `send`, and it holds with no `ChanInv` assumption and from the L0
interface alone: `send`'s own guard is what makes `deliver`'s push total. -/
theorem send_bounded (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c c' : Chan Q) (p : Frame)
    (h : send (E := E) c p = .ok c') :
    (QueueModel.toList (Q := Q) (α := E) c'.out).length + c'.inFlight ≤
      QueueModel.capacity (Q := Q) (α := E) c'.out := sorry

/-- `send` preserves the channel invariant, adding the frame to the pending list. The new frame's
`FrameOK` comes from `send`'s own length check, so there is no caller hypothesis on `p`. -/
theorem send_inv (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c c' : Chan Q) (ps : List Frame) (p : Frame)
    (hInv : ChanInv (E := E) c ps) (h : send (E := E) c p = .ok c') : ChanInv (E := E) c' (ps ++ [p]) := sorry

/-- The composite: delivering the oldest pending frame pushes exactly that frame onto the
abstract queue and keeps the invariant. Proved from the laws only. -/
theorem deliver_spec (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c : Chan Q) (p : Frame) (ps : List Frame) (hInv : ChanInv (E := E) c (p :: ps)) :
    ∃ c', deliver (E := E) c = .ok c' ∧
      QueueModel.toList (Q := Q) (α := E) c'.out =
        QueueModel.toList (Q := Q) (α := E) c.out ++ [FrameCarrier.ofFrame (E := E) p] ∧ ChanInv (E := E) c' ps := sorry

/-- The headline composite: from an idle channel, a successful `send` then `deliver` pushes exactly
`p` onto the abstract queue and returns the channel to idle. No `FrameOK p` hypothesis: `send`
refuses every payload outside it. -/
theorem send_deliver (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c c' : Chan Q) (p : Frame) (hInv : ChanInv (E := E) c [])
    (h : send (E := E) c p = .ok c') :
    ∃ c'', deliver (E := E) c' = .ok c'' ∧
      QueueModel.toList (Q := Q) (α := E) c''.out =
        QueueModel.toList (Q := Q) (α := E) c.out ++ [FrameCarrier.ofFrame (E := E) p] ∧ ChanInv (E := E) c'' [] := sorry

/-- `send` refuses every payload that is not `FrameOK`, i.e. of `2 ^ 32` bytes or more, whatever
the capacity: the Lean statement of the Rust length guard. -/
theorem send_refuses_too_long (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c : Chan Q) (p : Frame)
    (hp : ¬ FrameOK p) : send (E := E) c p = .fail := sorry
end FramedChannel.Channel

namespace FramedChannel.Channel
open FramedChannel

/-- `deliver_spec` at the ring buffer. -/
theorem deliver_spec_RB (c : Chan (RingBuffer.BQ Frame)) (p : Frame) (ps : List Frame)
    (h : ChanInv (E := Frame) c (p :: ps)) :
    ∃ c', deliver (E := Frame) c = .ok c' ∧ c'.out.1.contents = c.out.1.contents ++ [p] ∧ ChanInv (E := Frame) c' ps := sorry

/-- `deliver_spec` at the list-backed queue, with no reproof. -/
theorem deliver_spec_VQ (c : Chan (VecQueue.VQ Frame)) (p : Frame) (ps : List Frame)
    (h : ChanInv (E := Frame) c (p :: ps)) :
    ∃ c', deliver (E := Frame) c = .ok c' ∧ c'.out.items = c.out.items ++ [p] ∧ ChanInv (E := Frame) c' ps := sorry
end FramedChannel.Channel
