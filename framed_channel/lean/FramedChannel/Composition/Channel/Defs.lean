-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Queue
import FramedChannel.Model.Varint.Defs
import FramedChannel.Model.Crc8.Defs

/-!
# Composition/Channel/Defs: the channel definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of `Composition/Channel/Theorems.lean`: the wire
format (`marker`, `lenBytes`, `encodeFrame`, `encodeFrameTable`, `parseFrame`), the delivered
domain `FrameOK`, the `FrameCarrier` class and its identity instance, the channel state `Chan`,
its operations `send` and `deliver`, and the invariant `ChanInv`. It holds definitions only, so
that the Challenge module `FramedChannelChallenge.Channel` can import them without importing a
registered theorem.

Like the generic channel theorems, these definitions see the queue only through `Spec/Queue.lean`:
this module imports no queue model.
-/

namespace FramedChannel.Channel

open FramedChannel

/-! ## Wire format and the idealized frame round trip -/

abbrev Byte := BitVec 8
abbrev Frame := List Byte

/-- The frame boundary byte (`rust/src/channel.rs`'s `MARKER`). -/
def marker : Byte := 0x7E#8

/-- The varint length prefix as wire bytes (`encode_u32`). -/
def lenBytes (n : Nat) : List Byte := (Varint.encode n).map (BitVec.ofNat 8)

/-- One frame on the wire, as `Channel::send` writes it: marker, varint length, payload, CRC-8
of the payload (the bitwise `crc8`, which is what `channel.rs` calls). -/
def encodeFrame (p : Frame) : List Byte :=
  marker :: (lenBytes p.length ++ (p ++ [Crc8.crc8Bits p]))

/-- The same frame with the table-driven checksum `crc8_table`. -/
def encodeFrameTable (p : Frame) : List Byte :=
  marker :: (lenBytes p.length ++ (p ++ [Crc8.crc8Table p]))

/-- Idealized parse of one frame: a marker, a varint length `n`, `n` payload bytes and a check
byte that must equal the CRC-8 of the payload. Returns the payload and the rest of the wire. -/
def parseFrame : List Byte → Result (Frame × List Byte)
  | [] => .fail
  | m :: rest =>
    if m = marker then
      match Varint.decode (rest.map BitVec.toNat) with
      | .ok (n, rem) =>
        let bytes : List Byte := rem.map (BitVec.ofNat 8)
        match bytes.drop n with
        | c :: tl =>
          if (bytes.take n).length = n ∧ c = Crc8.crc8Bits (bytes.take n) then
            .ok (bytes.take n, tl)
          else .fail
        | [] => .fail
      | .fail => .fail
    else .fail

/-! ## Receiver model

The receiver reads one marker per frame and then reads the next byte as the first length byte,
whatever its value. `rust/src/channel.rs`'s `parse_frame` has the same shape, so `parseFrame`
above *is* the receiver: no side condition, no faithfulness gap, and no second parser to keep in
step with the first.

A payload of exactly 126 bytes has the marker `0x7E` as its single varint length byte -- the case
where a receiver that treated a second `0x7E` as a boundary would lose synchronization. Neither
this model nor the Rust does, and the model needs no `p.length ≠ 126` side condition;
`channel_len126_round_trips` in `rust/tests/differential.rs` is the executable check. -/

/-- The frames the channel is proved to deliver: the domain on which `parseFrame` and the Rust
`parse_frame` agree, with no cap beyond the varint's own. `send` establishes it: a payload outside
it is refused (`send_refuses_too_long`). -/
def FrameOK (p : Frame) : Prop := p.length < 2 ^ 32

/-- How a queue element carries a frame. -/
class FrameCarrier (E : Type) where
  ofFrame : Frame → E

instance : FrameCarrier Frame := ⟨id⟩

/-! ## The channel, generic over any bounded queue of frames -/

/-- The channel state: the output queue, the pending wire bytes, and the number of frames sent
but not yet delivered. Field for field `rust/src/channel.rs`'s `Channel<Q>`. -/
structure Chan (Q : Type) where
  out : Q
  wire : List Byte
  inFlight : Nat

section
variable {Q E : Type} [FrameCarrier E] [QueueModel Q E]

/-- `Channel::send`: refuse when `queued + in_flight ≥ capacity`, then refuse a payload of
`2 ^ 32` bytes or more (the complement of `FrameOK`, written literally because `FrameOK` carries no
`Decidable` instance), else append the frame to the wire and count it in flight. Both refusals are
the single `.fail`, as both are the Rust `Err(SendFail)`. -/
def send (c : Chan Q) (p : Frame) : Result (Chan Q) :=
  if (QueueModel.toList (Q := Q) (α := E) c.out).length + c.inFlight ≥
      QueueModel.capacity (Q := Q) (α := E) c.out then .fail
  else if 2 ^ 32 ≤ p.length then .fail
  else .ok { c with wire := c.wire ++ encodeFrame p, inFlight := c.inFlight + 1 }

/-- `Channel::deliver`: parse one frame off the wire, push it onto the output queue, and decrement
the in-flight count. Both failure branches are `.fail`, and `rust/src/channel.rs`'s `deliver`
returns `Err(DeliverFail)` in exactly those two cases. -/
def deliver (c : Chan Q) : Result (Chan Q) :=
  match parseFrame c.wire with
  | .ok (p, rest) =>
    match QueueModel.push c.out (FrameCarrier.ofFrame (E := E) p) with
    | .ok q' => .ok { out := q', wire := rest, inFlight := c.inFlight - 1 }
    | .fail => .fail
  | .fail => .fail

/-- The channel invariant, with the pending frames `ps` as a ghost list: the wire is exactly
their encodings, the in-flight count is their number, each is a frame the receiver delivers,
and the queue plus the frames in flight fit in the capacity. -/
def ChanInv (c : Chan Q) (ps : List Frame) : Prop :=
  c.wire = (ps.map encodeFrame).flatten ∧ c.inFlight = ps.length ∧
  (∀ p ∈ ps, FrameOK p) ∧
  (QueueModel.toList (Q := Q) (α := E) c.out).length + c.inFlight ≤
    QueueModel.capacity (Q := Q) (α := E) c.out

end

end FramedChannel.Channel
