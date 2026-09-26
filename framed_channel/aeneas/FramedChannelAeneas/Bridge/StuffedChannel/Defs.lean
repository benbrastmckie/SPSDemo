-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Channel.Defs
import FramedChannelAeneas.Bridge.Stuff.Defs
import FramedChannel.Composition.StuffedChannel.Defs

/-!
# Bridge/StuffedChannel/Defs: the transparent channel bridge's definitions

`[HAND-WRITTEN]` -- every definition a registered `StuffedChannel` bridge statement mentions:

* the relation `SChanRel` (`Abstraction.lean` beside this file explains the abstraction);
* `DeclaresWideLength` and the parser postcondition `ParsePost` (used by `Frame.lean`);
* the channel carriers `SChanRB` and `SChanVQ` (used by `Instance.lean`).

It holds definitions only, so that the Challenge module
`FramedChannelAeneasChallenge.StuffedChannel` can import them without importing a registered
theorem.

## What it reuses rather than redeclaring

Everything about *frames* and *queues* is `Bridge/Channel/Defs.lean`'s already: the frame carrier
`instFrameCarrierVecU8` at `alloc.vec.Vec Std.U8`, the extracted frame type `FrameVec`, the queue
carrier `ExtQ`, and the two extracted queue records `rbRecord` and `vqRecord`. A second
`FrameCarrier` instance at the same type would be a diamond, and a second copy of the queue
plumbing would be a second thing to keep in step. This unit's own content is the *wire*.

## Two byte views, deliberately

The specification `Chan` carries its wire as `List (BitVec 8)`; the specification `SChan` carries
its wire as `List Nat`, because a `CodecModel C (List Nat)` is what the composite is generic over
and because `Bridge/Stuff/` already reads machine bytes that way. So this bridge relates wires
through `Bridge.stuff.bytesOf` and payload frames through `Bridge.crc8.bitsOf`, and
`Abstraction.lean` carries the two lemmas that connect them.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Bridge.channel (ExtQ FrameVec frameClone frameDefault rbRecord vqRecord)

section
open FramedChannel.StuffedChannel (SChan)

variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]

/-- The extracted stuffed channel `c` is the specification channel `m` over the extracted carrier:
same queue state, same wire bytes (as naturals), same in-flight count. -/
def SChanRel {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
    (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) : Prop :=
  c.out = m.out.1 ∧ bytesOf c.wire.val = m.wire ∧ c.in_flight.val = m.inFlight

end

section
open FramedChannel.StuffedChannel (parseStuffed)

/-- The wire's leading stuffed frame unstuffs to a body whose length prefix decodes, in the model's
unbounded varint, to `2 ^ 32` or more: the one input on which the model's parser and the extracted
parser part ways. The stuffing layer contributes no such disjunct of its own --
`Bridge.stuff.decode_err_iff` is an exact iff -- so this is the varint layer's divergence and
nothing else. -/
def DeclaresWideLength (w : List Nat) : Prop :=
  ∃ bs rest n rem, FramedChannel.Stuff.decode w = .ok (bs, rest) ∧
    FramedChannel.Varint.decode bs = .ok (n, rem) ∧ 2 ^ 32 ≤ n

/-- How the extracted parser's result relates to the specification's `parseStuffed` on the same wire
bytes. `some (v, used)`: the specification parses the same payload and leaves exactly the bytes
after `used`. `none`: the specification fails too, **or** the frame declares a length of `2 ^ 32` or
more. That second disjunct is a real divergence, stated rather than hidden: the model's varint
decoder works over `Nat` and accepts such a length, while the extracted `decode_u32` rejects it as
`Overlong`. No frame the channel writes declares one (`FrameOK`). -/
def ParsePost (w : List Nat) : WP.Post (Option (alloc.vec.Vec Std.U8 × Std.Usize))
  | some (v, used) => used.val ≤ w.length ∧
      parseStuffed (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) w
        = .ok (bitsOf v.val, w.drop used.val)
  | none => parseStuffed (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise) w = .fail
      ∨ DeclaresWideLength w

end

section
open FramedChannel.StuffedChannel (SChan)

/-- The specification stuffed channel over the extracted ring buffer. -/
abbrev SChanRB : Type :=
  SChan (ExtQ (ring_buffer.RingBuffer FrameVec) (FramedChannel.RingBuffer.BQ FrameVec) rbRecord
    (fun s q => ring_buffer.toModel s = q.1))
/-- The specification stuffed channel over the extracted `VecQueue`. -/
abbrev SChanVQ : Type :=
  SChan (ExtQ (queue.VecQueue FrameVec) (FramedChannel.VecQueue.VQ FrameVec) vqRecord
    (fun s q => vec_queue.toModel s = q))

end

end FramedChannel.Bridge.stuffed_channel
