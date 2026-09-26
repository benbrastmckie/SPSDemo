-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.StuffedChannel.Defs
import FramedChannel.Composition.Receiver.Defs

/-!
# Bridge/Receiver/Defs: the resynchronizing receive path bridge's definitions

`[HAND-WRITTEN]` -- every definition a registered `Receiver` bridge statement mentions:

* the relation `RcvRel` (the abstraction from the extracted `Receiver<Q>` record to the
  specification `Rcv`);
* the receiver carriers `RcvRB` and `RcvVQ` (used by `Instance.lean`);
* `NoWideRun`, `feed`'s wide-length side condition. It is stated entirely in model terms, and it
  sits here rather than in `Loop.lean` beside the loop that consumes it precisely because
  `feed_refines` is registered and mentions it: a definition a registered statement names has to be
  reachable from the Challenge module, which imports no module holding a proof.

It holds definitions only, so that the Challenge module `FramedChannelAeneasChallenge.Receiver` can
import them without importing a registered theorem.

## What it reuses rather than redeclaring

Almost everything. Frames and queues come from `Bridge/Channel/Defs.lean`: the frame carrier
`instFrameCarrierVecU8` at `alloc.vec.Vec Std.U8`, the extracted frame type `FrameVec`, the queue
carrier `ExtQ`, and the two extracted queue records `rbRecord` and `vqRecord`. The *run parse* comes
from `Bridge/StuffedChannel/`: `ParsePost`, `DeclaresWideLength` and the already-proved
`parse_stuffed_refines`, because `finish_run` calls `stuffed_channel::parse_stuffed` and nothing else
-- which is the whole reason this bridge is four modules rather than five. Byte views come from
`Bridge/Stuff/`'s `bytesOf` and `Bridge/Crc8/`'s `bitsOf`.

A second `FrameCarrier` instance at the same type would be a diamond; a second copy of the queue
plumbing or of the run parser would be a second thing to keep in step. This unit's own content is
the *scan*.

## The abstraction

`RcvRel` is three equations, one per field, and the middle one is the only interesting choice: the
extracted `buf` is a `Vec<u8>` and the specification `buf` is a `List Nat`, so the two are related
through `bytesOf`, exactly as `SChanRel` relates the two wires. The output queue is related by
`Ext`'s own projection (`c.out = m.out.1`), as every other composite's relation does, and the drop
counter by `Usize`'s value.

Note what `RcvRel` does NOT say: nothing bounds `buf`. A wire carrying no flag grows it, and Aeneas
bounds a `Vec` by `Usize.max`, which is where `feed`'s single hypothesis comes from in
`Refinement.lean`. That hypothesis is on the fed slice's length plus the buffer's, not on the
relation.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.receiver
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.channel (ExtQ FrameVec rbRecord vqRecord)

section
open FramedChannel.Receiver (Rcv)

variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]

/-- The extracted receiver `c` is the specification receiver `m` over the extracted carrier: same
queue state, same buffered run (as naturals), same drop count. -/
def RcvRel {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
    (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) : Prop :=
  c.out = m.out.1 ∧ bytesOf c.buf.val = m.buf ∧ c.dropped.val = m.dropped

/-- No run this receiver will judge declares a length of `2 ^ 32` or more: the `DeclaresWideLength`
disjunct `finish_run` inherits from the reused run parser, quantified over every prefix of the fed
wire. `finish_run_refines` can state that disjunct in its postcondition because it judges one run;
`feed` judges many, so it takes this as a hypothesis instead. Stated in model terms only, so a client
discharges it by knowing what it fed. -/
def NoWideRun {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
    (bytes : Slice Std.U8) (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) : Prop :=
  ∀ k, k ≤ bytes.val.length →
    ¬ FramedChannel.Bridge.stuffed_channel.DeclaresWideLength
      ((FramedChannel.Receiver.feed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker m
          ((bytesOf bytes.val).take k)).buf ++ [FramedChannel.Stuff.marker])

end

section
open FramedChannel.Receiver (Rcv)

/-- The specification receiver over the extracted ring buffer. -/
abbrev RcvRB : Type :=
  Rcv (ExtQ (ring_buffer.RingBuffer FrameVec) (FramedChannel.RingBuffer.BQ FrameVec) rbRecord
    (fun s q => ring_buffer.toModel s = q.1))
/-- The specification receiver over the extracted `VecQueue`. -/
abbrev RcvVQ : Type :=
  Rcv (ExtQ (queue.VecQueue FrameVec) (FramedChannel.VecQueue.VQ FrameVec) vqRecord
    (fun s q => vec_queue.toModel s = q))

end

end FramedChannel.Bridge.receiver
