-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Queue
import FramedChannel.Spec.Codec
import FramedChannel.Spec.Checksum
import FramedChannel.Model.Varint.Defs
import FramedChannel.Composition.Channel.Defs

/-!
# Composition/StuffedChannel/Defs: the transparent channel's definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of
`Composition/StuffedChannel/Theorems.lean`: the composition-layer law bundle `Transparent`, the
frame body `body`, the stuffed wire format (`encodeStuffed`, `parseStuffed`), the channel state
`SChan`, its operations `send` and `deliver`, and the invariant `SChanInv`. It holds definitions
only, so that the Challenge module `FramedChannelChallenge.StuffedChannel` can import them without
importing a registered theorem.

## What this composite is, and how it differs from `Channel`

`Channel` writes a raw frame behind a boundary byte, so a `0x7E` inside a frame's length bytes,
payload or check byte is data and the framing offers no transparency. `StuffedChannel` passes the
whole frame *body* through a self-delimiting codec instead, and the codec is reached only through
`Spec/Codec.lean`. At `Stuff.Hdlc` that codec is HDLC byte stuffing, and the wire it writes
contains the flag byte nowhere but at the frame terminator -- the property `Channel` cannot have.

## Which interfaces this reaches, and why `CodecLaws` is not one of them

Three interfaces, generically: `QueueModel`/`BoundedQueueLaws` for the output queue,
`CodecModel` at L0 for the framing codec, and `ChecksumModel` at L0 for the check byte. The L1
codec laws `CodecLaws` are deliberately *not* used, because they are too weak twice over: the
`Dom` of `Stuff.instCodecLaws` caps payloads at 255 bytes where this composite (like `Channel`)
admits every payload below `2 ^ 32`, and its `round_trip` gives a residual of `[]` only, which
would confine the invariant to at most one pending frame. What the composite actually needs is the
bundle `Transparent` below: the same round trip *with an arbitrary residual*, plus the two facts
that make the wire scannable. It is discharged in
`Composition/StuffedChannel/Instances.lean` from `Stuff.unstuff_stuff` and
`Stuff.stuff_marker_free`, both already proved in the model layer.

No `ChecksumLaws` law is used either: the round trip needs only that the same `digest` is applied
on both sides, never `digest_nil` or `digest_snoc`. `Varint` is reached monomorphically through
`Varint.varint_roundtrip`, exactly as `Channel` reaches it.

Like the generic channel definitions, these see the queue only through `Spec/Queue.lean`: this
module imports no queue model.
-/

namespace FramedChannel.StuffedChannel

open FramedChannel
open FramedChannel.Channel (Byte Frame FrameOK FrameCarrier lenBytes)

/-! ## The composition-layer transparency bundle

`flag` is a class *parameter* rather than a field: a `Prop`-valued class cannot carry a `Nat`
field. `FrameCarrier` in `Composition/Channel/Defs.lean` is the existing precedent for a law
bundle that lives at the composition layer rather than in `Spec/`. -/

/-- What the composite needs of its framing codec, beyond `CodecModel`'s operations: a round trip
that tolerates an arbitrary residual, a body containing the flag byte nowhere, and a terminating
flag. `CodecLaws` gives none of the three in this form -- see the module docstring. -/
class Transparent (C : Type) [CodecModel C (List Nat)] (flag : Nat) : Prop where
  /-- The round trip with an arbitrary residual: whatever follows a complete encoding is returned
  untouched. `CodecLaws.round_trip` gives this only with residual `[]`, and only on `Dom`. -/
  decode_append : ∀ p rest : List Nat,
    CodecModel.decode (C := C) (CodecModel.encode (C := C) p ++ rest) = .ok (p, rest)
  /-- Transparency: no byte of the encoding but the last is the flag. -/
  body_flag_free : ∀ p : List Nat, ∀ c ∈ (CodecModel.encode (C := C) p).dropLast, c ≠ flag
  /-- Self-delimitation: the encoding ends with the flag. -/
  ends_with_flag : ∀ p : List Nat, (CodecModel.encode (C := C) p).getLast? = some flag

/-! ## The stuffed wire format -/

section defs
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]

/-- The frame body, before framing: varint length, payload, check byte. The same three layers
`Channel.encodeFrame` composes, but reached through the checksum interface rather than through
`Crc8` directly, and carrying no leading boundary byte -- the codec's terminating flag is the only
delimiter. -/
def body (p : Frame) : List Nat :=
  (lenBytes p.length ++ (p ++ [ChecksumModel.digest (C := K) p])).map BitVec.toNat

/-- One frame on the wire, as `StuffedChannel::send` writes it: the body, framed by the codec. At
`C := Stuff.Hdlc` that is the body byte-stuffed and terminated by the flag. -/
def encodeStuffed (p : Frame) : List Nat := CodecModel.encode (C := C) (body (K := K) p)

/-- Parse of one stuffed frame: unframe with the codec, read a varint length `n`, take exactly `n`
payload bytes and one check byte that must equal the payload's digest, with nothing left over.
Returns the payload and the rest of the wire. -/
def parseStuffed (w : List Nat) : Result (Frame × List Nat) :=
  match CodecModel.decode (C := C) w with
  | .ok (bs, rest) =>
    match Varint.decode bs with
    | .ok (n, rem) =>
      let bytes : Frame := rem.map (BitVec.ofNat 8)
      match bytes.drop n with
      | [c] => if (bytes.take n).length = n ∧ c = ChecksumModel.digest (C := K) (bytes.take n)
               then .ok (bytes.take n, rest) else .fail
      | _ => .fail
    | .fail => .fail
  | .fail => .fail

/-! ## The stuffed channel, generic over any bounded queue of frames -/

/-- The stuffed channel state: the output queue, the pending wire bytes, and the number of frames
sent but not yet delivered. Field for field `rust/src/stuffed_channel.rs`'s `StuffedChannel<Q>`. -/
structure SChan (Q : Type) where
  out : Q
  wire : List Nat
  inFlight : Nat

variable {Q E : Type} [FrameCarrier E] [QueueModel Q E]

/-- `StuffedChannel::send`: refuse when `queued + in_flight ≥ capacity`, then refuse a payload of
`2 ^ 32` bytes or more (the complement of `FrameOK`, written literally because `FrameOK` carries no
`Decidable` instance), else append the stuffed frame to the wire and count it in flight. Both
refusals are the single `.fail`, as both are the Rust `Err(SendFail)`. -/
def send (c : SChan Q) (p : Frame) : Result (SChan Q) :=
  if (QueueModel.toList (Q := Q) (α := E) c.out).length + c.inFlight ≥
      QueueModel.capacity (Q := Q) (α := E) c.out then .fail
  else if 2 ^ 32 ≤ p.length then .fail
  else .ok { c with wire := c.wire ++ encodeStuffed (C := C) (K := K) p,
                    inFlight := c.inFlight + 1 }

/-- `StuffedChannel::deliver`: read one stuffed frame off the wire, push its payload onto the
output queue, and decrement the in-flight count. Both failure branches are `.fail`, and
`rust/src/stuffed_channel.rs`'s `deliver` returns `Err(DeliverFail)` in exactly those two cases. -/
def deliver (c : SChan Q) : Result (SChan Q) :=
  match parseStuffed (C := C) (K := K) c.wire with
  | .ok (p, rest) =>
    match QueueModel.push c.out (FrameCarrier.ofFrame (E := E) p) with
    | .ok q' => .ok { out := q', wire := rest, inFlight := c.inFlight - 1 }
    | .fail => .fail
  | .fail => .fail

/-- The channel invariant, with the pending frames `ps` as a ghost list: the wire is exactly their
stuffed encodings, the in-flight count is their number, each is a frame the receiver delivers, and
the queue plus the frames in flight fit in the capacity. -/
def SChanInv (c : SChan Q) (ps : List Frame) : Prop :=
  c.wire = (ps.map (encodeStuffed (C := C) (K := K))).flatten ∧ c.inFlight = ps.length ∧
  (∀ p ∈ ps, FrameOK p) ∧
  (QueueModel.toList (Q := Q) (α := E) c.out).length + c.inFlight ≤
    QueueModel.capacity (Q := Q) (α := E) c.out

end defs

end FramedChannel.StuffedChannel
