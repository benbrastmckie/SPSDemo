-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Receiver.Defs

/-!
# FramedChannelAeneasChallenge.Receiver: approved statements (extracted receive path)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/Receiver/{Loop,Refinement,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.

Eleven statements, where the transparent channel's module carries twenty-four. That is the reuse the
plan bought rather than an omission: the *run* parse is `stuffed_channel.parse_stuffed`, already
approved in `FramedChannelAeneasChallenge.StuffedChannel`, so what is restated here is the scan --
the loop's run judgement `finish_run_refines`, the four operations over any lawful queue record, and
the substitution rows at both extracted queues.

`feed_refines` carries three hypotheses. Two are `usize` bounds on real memory, and the third,
`NoWideRun`, is the `DeclaresWideLength` disjunct inherited from the reused run parser, quantified
over every prefix of the fed wire. It is a *definition* (`Bridge/Receiver/Defs.lean`), which is why
that module holds it rather than `Loop.lean`: a definition a registered statement names must be
reachable from here, and this module imports no module holding a proof.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.receiver
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.stuffed_channel (DeclaresWideLength)
open FramedChannel.Receiver (Rcv finishRun)
section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
include hsim

/-- The run judgement, the loop's own step lemma: the extracted `finish_run` leaves a receiver
related to the model's `finishRun` of the buffered run terminated by one flag -- **or** that run
declares a length of `2 ^ 32` or more, the divergence disjunct inherited from the reused run parser
(`stuffed_channel.parse_stuffed`). The two hypotheses are the panic obligation of `Vec::push` and the
bound that makes the two drop counters *agree*: `dropped.saturating_add(1)` is total, so nothing
panics, but it caps at `Usize.max` where the model's `Nat` does not. `finish_run` is private in Rust
and is covered by this row rather than by a differential vector. `[EXTRACTED: aeneas + bridge]` -/
theorem finish_run_refines (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : RcvRel c m)
    (hbuf : c.buf.val.length < Usize.max) (hdropmax : c.dropped.val < Usize.max) :
    receiver.Receiver.finish_run inst c ⦃ c' =>
      DeclaresWideLength (m.buf ++ [FramedChannel.Stuff.marker]) ∨
        RcvRel c' (finishRun (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker m) ⦄ := sorry
end
end FramedChannel.Bridge.receiver

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.receiver
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Receiver (Rcv)
section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hsim hfun

omit hfun in
/-- Feed refinement, over any lawful extracted queue record: the extracted `feed` leaves a receiver
related to the model's fold over the same bytes. Three hypotheses, each genuine extracted behaviour:
the buffered run plus the fed bytes fit a `usize` (`Vec::push`); the drop count plus the fed bytes fit
a `usize` (`saturating_add` bought panic-freedom, not value agreement); and no run this receiver will
judge declares a length of `2 ^ 32` or more. `[EXTRACTED: aeneas + bridge]` -/
theorem feed_refines (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (bytes : Slice Std.U8)
    (hR : RcvRel c m) (hnw : NoWideRun bytes m)
    (hbufw : c.buf.val.length + bytes.val.length ≤ Usize.max)
    (hdropw : c.dropped.val + bytes.val.length ≤ Usize.max) :
    receiver.Receiver.feed inst c bytes ⦃ c' =>
      RcvRel c' (FramedChannel.Receiver.feed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8)
        FramedChannel.Stuff.marker m (bytesOf bytes.val)) ⦄ := sorry

omit hfun in
/-- Poll refinement: the extracted `poll` hands back exactly what the specification's queue pops, and
returns `None` with the receiver unchanged exactly when the specification's pop fails.
`[EXTRACTED: aeneas + bridge]` -/
theorem poll_refines (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : RcvRel c m) :
    receiver.Receiver.poll inst c ⦃ o c' =>
      (∀ y m', FramedChannel.Receiver.poll (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
          (E := alloc.vec.Vec Std.U8) m = .ok (y, m') → o = some y ∧ RcvRel c' m') ∧
      (FramedChannel.Receiver.poll (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
          (E := alloc.vec.Vec Std.U8) m = .fail → o = none ∧ c' = c) ⦄ := sorry

omit hfun hsim in
/-- `dropped` is the specification's drop count. `[EXTRACTED: aeneas + bridge]` -/
theorem dropped_agrees (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : RcvRel c m) :
    receiver.Receiver.impl.dropped inst c ⦃ n => n.val = m.dropped ⦄ := sorry

/-- `queued` is the length of the specification queue's contents. `[EXTRACTED: aeneas + bridge]` -/
theorem queued_agrees (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : RcvRel c m) :
    receiver.Receiver.queued inst c ⦃ n =>
      n.val = (QueueModel.toList (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
        (α := alloc.vec.Vec Std.U8) m.out).length ⦄ := sorry
end
end FramedChannel.Bridge.receiver

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.receiver
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.channel (FrameVec rbRecord vqRecord)
open FramedChannel.Receiver (Rcv)

/-- `Receiver::new` (the ring buffer receiver) starts idle, at every capacity.
`[EXTRACTED: aeneas + bridge]` -/
theorem new_idle_RB (cap : Std.Usize) :
    receiver.ReceiverRingBufferVecU8.new cap ⦃ c => ∃ m : RcvRB, RcvRel c m ∧ m.buf = [] ∧
      m.dropped = 0 ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := sorry

/-- `Receiver::with_queue` at the `VecQueue` record starts idle. `[EXTRACTED: aeneas + bridge]` -/
theorem with_queue_idle_VQ (cap : Std.Usize) :
    receiver.Receiver.with_queue vqRecord cap ⦃ c => ∃ m : RcvVQ, RcvRel c m ∧ m.buf = [] ∧
      m.dropped = 0 ∧ QueueModel.toList (α := FrameVec) m.out = [] ⦄ := sorry

/-- `feed_refines` at the extracted ring buffer: no simulation hypothesis remains.
`[EXTRACTED: aeneas + bridge]` -/
theorem feed_refines_RB (c : receiver.Receiver (ring_buffer.RingBuffer FrameVec)) (m : RcvRB)
    (bytes : Slice Std.U8) (hR : RcvRel c m) (hnw : NoWideRun bytes m)
    (hbufw : c.buf.val.length + bytes.val.length ≤ Usize.max)
    (hdropw : c.dropped.val + bytes.val.length ≤ Usize.max) :
    receiver.Receiver.feed rbRecord c bytes ⦃ c' =>
      RcvRel c' (FramedChannel.Receiver.feed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := FrameVec)
        FramedChannel.Stuff.marker m (bytesOf bytes.val)) ⦄ := sorry

/-- The same proof at the extracted `VecQueue`, with no reproof. `[EXTRACTED: aeneas + bridge]` -/
theorem feed_refines_VQ (c : receiver.Receiver (queue.VecQueue FrameVec)) (m : RcvVQ)
    (bytes : Slice Std.U8) (hR : RcvRel c m) (hnw : NoWideRun bytes m)
    (hbufw : c.buf.val.length + bytes.val.length ≤ Usize.max)
    (hdropw : c.dropped.val + bytes.val.length ≤ Usize.max) :
    receiver.Receiver.feed vqRecord c bytes ⦃ c' =>
      RcvRel c' (FramedChannel.Receiver.feed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := FrameVec)
        FramedChannel.Stuff.marker m (bytesOf bytes.val)) ⦄ := sorry

/-- `poll_refines` at the extracted ring buffer. `[EXTRACTED: aeneas + bridge]` -/
theorem poll_refines_RB (c : receiver.Receiver (ring_buffer.RingBuffer FrameVec)) (m : RcvRB)
    (hR : RcvRel c m) :
    receiver.Receiver.poll rbRecord c ⦃ o c' =>
      (∀ y m', FramedChannel.Receiver.poll (E := FrameVec) m = .ok (y, m') →
        o = some y ∧ RcvRel c' m') ∧
      (FramedChannel.Receiver.poll (E := FrameVec) m = .fail → o = none ∧ c' = c) ⦄ := sorry

/-- The same proof at the extracted `VecQueue`, with no reproof. `[EXTRACTED: aeneas + bridge]` -/
theorem poll_refines_VQ (c : receiver.Receiver (queue.VecQueue FrameVec)) (m : RcvVQ)
    (hR : RcvRel c m) :
    receiver.Receiver.poll vqRecord c ⦃ o c' =>
      (∀ y m', FramedChannel.Receiver.poll (E := FrameVec) m = .ok (y, m') →
        o = some y ∧ RcvRel c' m') ∧
      (FramedChannel.Receiver.poll (E := FrameVec) m = .fail → o = none ∧ c' = c) ⦄ := sorry
end FramedChannel.Bridge.receiver
