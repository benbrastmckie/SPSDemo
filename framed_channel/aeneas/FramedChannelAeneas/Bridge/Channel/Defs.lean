-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Defs
import FramedChannelAeneas.Bridge.RingBuffer.Defs
import FramedChannelAeneas.Bridge.VecQueue.Defs
import FramedChannelAeneas.Bridge.Crc8.Defs
import FramedChannelAeneas.Bridge.Varint.Defs
import FramedChannel.Composition.Channel.Defs

/-!
# Bridge/Channel/Defs: the channel bridge's definitions

`[HAND-WRITTEN]` -- every definition a registered channel bridge statement mentions:

* `vecOfFrame`, the `FrameCarrier` instance at `alloc.vec.Vec Std.U8`, and the relation `ChanRel`
  (`Abstraction.lean` beside this file explains the abstraction);
* `DeclaresWideLength` and the parser postcondition `ParsePost` (used by `Frame.lean`);
* the queue carrier `ExtQ` (used by `Composite.lean`);
* the frame type `FrameVec`, its `Clone` and `Default` records, the two extracted queue records
  and the channel carriers `ChanRB` and `ChanVQ` (used by `Instance.lean`).

It holds definitions only, so that the Challenge module `FramedChannelAeneasChallenge.Channel` can
import them without importing a registered theorem. Each group sits in its own section with its
own `open` lines.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)

section
open FramedChannel.Channel (Frame Chan FrameCarrier FrameOK)

/-- A frame as a vector of machine bytes, when it fits. -/
def vecOfFrame (p : Frame) : alloc.vec.Vec Std.U8 :=
  if h : p.length ≤ Usize.max then
    alloc.vec.Vec.from (p.map fun b => (⟨b⟩ : Std.U8)) (by simpa using h)
  else alloc.vec.Vec.new Std.U8

instance instFrameCarrierVecU8 : FrameCarrier (alloc.vec.Vec Std.U8) := ⟨vecOfFrame⟩

variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]

/-- The extracted channel `c` is the specification channel `m` over the extracted carrier: same
queue state, same wire bytes, same in-flight count. -/
def ChanRel {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
    (c : channel.Channel S) (m : Chan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) : Prop :=
  c.out = m.out.1 ∧ bitsOf c.wire.val = m.wire ∧ c.in_flight.val = m.inFlight

end

section
open FramedChannel.Channel (marker parseFrame encodeFrame lenBytes)

/-- The wire starts with a frame whose length prefix decodes, in the model's unbounded varint, to
`2 ^ 32` or more: the one input on which the model's parser and the extracted parser part ways. -/
def DeclaresWideLength (w : List (BitVec 8)) : Prop :=
  ∃ rest n rem, w = marker :: rest ∧
    FramedChannel.Varint.decode (rest.map BitVec.toNat) = .ok (n, rem) ∧ 2 ^ 32 ≤ n

/-- How the extracted parser's result relates to the specification's `parseFrame` on the same wire
bytes. `some (payload, used)`: the specification parses the same payload and leaves exactly the
bytes after `used`. `none`: the specification fails too, **or** the frame declares a length of
`2 ^ 32` or more. That second disjunct is a real divergence, stated rather than hidden: the model's
varint decoder works over `Nat` and accepts such a length, while the extracted `decode_u32`
rejects it as `Overlong`. No frame the channel writes declares one (`FrameOK`). -/
def ParsePost (w : List (BitVec 8)) : WP.Post (Option (alloc.vec.Vec Std.U8 × Std.Usize))
  | some (v, used) => used.val ≤ w.length ∧ parseFrame w = .ok (bitsOf v.val, w.drop used.val)
  | none => parseFrame w = .fail ∨ DeclaresWideLength w

end

section
open FramedChannel.Channel (Chan FrameCarrier FrameOK ChanInv encodeFrame parseFrame)

/-- The specification channel's queue carrier over the extracted record: `Bridge/Queue/Instance.lean`'s
`Ext` at the frame element type. -/
abbrev ExtQ (S Q : Type) [QueueModel Q (alloc.vec.Vec Std.U8)] (inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8))
    (R : S → Q → Prop) : Type := Ext S Q (alloc.vec.Vec Std.U8) inst R

/-- The extracted frame type, `Vec<u8>`. -/
abbrev FrameVec := alloc.vec.Vec Std.U8
/-- The derived `Clone` of `Vec<u8>`, as the extraction passes it. -/
abbrev frameClone : core.clone.Clone FrameVec := core.clone.CloneallocvecVec core.clone.CloneU8
/-- `Default` for `Vec<u8>`, as `Channel::new` passes it. -/
abbrev frameDefault : core.default.Default FrameVec := alloc.vec.Vec.Insts.CoreDefaultDefault Std.U8
/-- The extracted `BoundedQueue` record of the ring buffer at the frame type, exactly the one
`channel.ChannelRingBufferVecU8.new` builds. -/
abbrev rbRecord : queue.BoundedQueue (ring_buffer.RingBuffer FrameVec) FrameVec :=
  ring_buffer.RingBuffer.Insts.Framed_channelQueueBoundedQueue frameDefault frameClone
/-- The extracted `BoundedQueue` record of `VecQueue` at the frame type. -/
abbrev vqRecord : queue.BoundedQueue (queue.VecQueue FrameVec) FrameVec :=
  queue.VecQueue.Insts.Framed_channelQueueBoundedQueue frameClone
/-- The specification channel over the extracted ring buffer. -/
abbrev ChanRB : Type :=
  Chan (ExtQ (ring_buffer.RingBuffer FrameVec) (FramedChannel.RingBuffer.BQ FrameVec) rbRecord
    (fun s q => ring_buffer.toModel s = q.1))
/-- The specification channel over the extracted `VecQueue`. -/
abbrev ChanVQ : Type :=
  Chan (ExtQ (queue.VecQueue FrameVec) (FramedChannel.VecQueue.VQ FrameVec) vqRecord
    (fun s q => vec_queue.toModel s = q))

end

end FramedChannel.Bridge.channel
