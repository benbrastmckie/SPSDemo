-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Composition.StuffedChannel.Defs
import FramedChannel.Model.Stuff.Defs
import FramedChannel.Model.Crc8.Defs
import FramedChannel.Model.RingBuffer.Defs
import FramedChannel.Model.VecQueue.Defs

/-!
# FramedChannelChallenge.StuffedChannel: approved statements (transparent channel composite)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Composition/StuffedChannel/Theorems.lean` and
`Composition/StuffedChannel/Instances.lean`. See `lean/FramedChannelChallenge.lean` for what a
Challenge module is and what the gate checks.

`instTransparentHdlc` is admissible here because `Transparent` is `Prop`-valued: a Challenge module
may hold no non-`Prop` instance, exactly as `FramedChannelChallenge.Stuff`'s `instCodecLaws` is
admissible.
-/

namespace FramedChannel.StuffedChannel
open FramedChannel
open FramedChannel.Channel (Byte Frame FrameOK FrameCarrier)

section
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]

/-- Transparency round trip: one frame recovered off a stuffed wire, at every payload including one
containing the flag byte, with no marker-freedom hypothesis. Composed from the codec's
`decode_append` and `Varint.varint_roundtrip`. -/
theorem parseStuffed_encodeStuffed (flag : Nat) [Transparent C flag]
    (p : Frame) (rest : List Nat) (hp : p.length < 2 ^ 32) :
    parseStuffed (C := C) (K := K) (encodeStuffed (C := C) (K := K) p ++ rest)
      = .ok (p, rest) := sorry

/-- TRANSPARENCY, the theorem `Channel` cannot have: every byte the channel has written other than
the frame terminator is not the flag, so a receiver may scan to the next flag. -/
theorem wire_flag_free_of_send (flag : Nat) [Transparent C flag] (p : Frame) :
    ∀ b ∈ (encodeStuffed (C := C) (K := K) p).dropLast, b ≠ flag := sorry

/-- The capacity check of `send` discharges `push`'s not-full assumption. -/
theorem send_discharges_not_full (Q E : Type) [FrameCarrier E] [QueueModel Q E]
    [BoundedQueueLaws Q E] (c c' : SChan Q) (p : Frame)
    (h : send (C := C) (K := K) (E := E) c p = .ok c') :
    ¬ QueueModel.full (Q := Q) (α := E) c.out := sorry

/-- Bounds: after a successful `send`, queued plus in-flight is still within the capacity. It holds
with no `SChanInv` assumption and from the L0 interface alone: `send`'s own guard is what makes
`deliver`'s push total. -/
theorem send_bounded (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c c' : SChan Q) (p : Frame)
    (h : send (C := C) (K := K) (E := E) c p = .ok c') :
    (QueueModel.toList (Q := Q) (α := E) c'.out).length + c'.inFlight ≤
      QueueModel.capacity (Q := Q) (α := E) c'.out := sorry

/-- `send` refuses every payload that is not `FrameOK`, i.e. of `2 ^ 32` bytes or more, whatever the
capacity: the Lean statement of the Rust length guard. -/
theorem send_refuses_too_long (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c : SChan Q)
    (p : Frame) (hp : ¬ FrameOK p) : send (C := C) (K := K) (E := E) c p = .fail := sorry

/-- `send` preserves the channel invariant, adding the frame to the pending list. The new frame's
`FrameOK` comes from `send`'s own length check, so there is no caller hypothesis on `p`. -/
theorem send_inv (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c c' : SChan Q) (ps : List Frame) (p : Frame)
    (hInv : SChanInv (C := C) (K := K) (E := E) c ps)
    (h : send (C := C) (K := K) (E := E) c p = .ok c') :
    SChanInv (C := C) (K := K) (E := E) c' (ps ++ [p]) := sorry

/-- The composite: delivering the oldest pending frame pushes exactly that frame onto the abstract
queue and keeps the invariant. Proved from the queue laws, the codec's `Transparent` bundle and the
checksum interface only. -/
theorem deliver_spec (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (flag : Nat) [Transparent C flag] (c : SChan Q) (p : Frame) (ps : List Frame)
    (hInv : SChanInv (C := C) (K := K) (E := E) c (p :: ps)) :
    ∃ c', deliver (C := C) (K := K) (E := E) c = .ok c' ∧
      QueueModel.toList (Q := Q) (α := E) c'.out =
        QueueModel.toList (Q := Q) (α := E) c.out ++ [FrameCarrier.ofFrame (E := E) p] ∧
      SChanInv (C := C) (K := K) (E := E) c' ps := sorry

/-- The headline composite: from an idle channel, a successful `send` then `deliver` pushes exactly
`p` onto the abstract queue and returns the channel to idle. No `FrameOK p` hypothesis: `send`
refuses every payload outside it. -/
theorem send_deliver (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (flag : Nat) [Transparent C flag] (c c' : SChan Q) (p : Frame)
    (hInv : SChanInv (C := C) (K := K) (E := E) c [])
    (h : send (C := C) (K := K) (E := E) c p = .ok c') :
    ∃ c'', deliver (C := C) (K := K) (E := E) c' = .ok c'' ∧
      QueueModel.toList (Q := Q) (α := E) c''.out =
        QueueModel.toList (Q := Q) (α := E) c.out ++ [FrameCarrier.ofFrame (E := E) p] ∧
      SChanInv (C := C) (K := K) (E := E) c'' [] := sorry

end
end FramedChannel.StuffedChannel

namespace FramedChannel.StuffedChannel
open FramedChannel
open FramedChannel.Channel (Frame)

/-- The composition-layer transparency bundle, discharged at HDLC stuffing. `decode_append` is
`Stuff.unstuff_stuff`'s loop invariant at the empty accumulator; `body_flag_free` is
`Stuff.stuff_marker_free` after dropping the terminating flag; `ends_with_flag` is the shape of
`Stuff.encode` itself. -/
instance instTransparentHdlc : Transparent Stuff.Hdlc Stuff.marker := sorry

/-- `deliver_spec` at the ring buffer, HDLC framing, bitwise CRC-8. -/
theorem deliver_spec_RB (c : SChan (RingBuffer.BQ Frame)) (p : Frame) (ps : List Frame)
    (h : SChanInv (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c (p :: ps)) :
    ∃ c', deliver (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c = .ok c' ∧
      c'.out.1.contents = c.out.1.contents ++ [p] ∧
      SChanInv (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c' ps := sorry

/-- The same proof at the list-backed queue, with no reproof. -/
theorem deliver_spec_VQ (c : SChan (VecQueue.VQ Frame)) (p : Frame) (ps : List Frame)
    (h : SChanInv (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c (p :: ps)) :
    ∃ c', deliver (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c = .ok c' ∧
      c'.out.items = c.out.items ++ [p] ∧
      SChanInv (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c' ps := sorry

end FramedChannel.StuffedChannel
