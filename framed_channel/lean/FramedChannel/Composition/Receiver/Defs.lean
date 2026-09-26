-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Receiver
import FramedChannel.Composition.StuffedChannel.Defs
import FramedChannel.Model.Stuff.Defs
import FramedChannel.Model.Crc8.Defs

/-!
# Composition/Receiver/Defs: the resynchronizing receive path's definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of
`Composition/Receiver/Theorems.lean`: the receiver state `Rcv`, its per-run acceptance test
`acceptRun`, the run terminator `finishRun`, the one-byte transition `step`, the stream operation
`feed`, the observations `accepted`, `dropped`, `room` and `quiet`, `poll`, and the sender-wire
decomposition `EncRun`. It holds definitions only, so that the Challenge module
`FramedChannelChallenge.Receiver` can import them without importing a registered theorem.

## Why this is a composition, and why it lives here rather than under `Model/`

The receiver's per-run acceptance test *is* `StuffedChannel.parseStuffed`. That is not a
convenience: resynchronization is sound only because a stuffed body is marker-free, so a flag byte
on the wire is unambiguously a frame boundary and never payload data. The composition-layer
`Transparent` bundle's `body_flag_free` is therefore the load-bearing hypothesis of
`Composition/Receiver/Theorems.lean`'s soundness theorem rather than a decorative lemma, and
`Evidence/Countermodels.lean` refutes the corresponding claim over `Channel`'s unstuffed framing in
the kernel.

Because the per-run parse is a composition, this unit cannot live under `Model/`:
`check.sh`'s layer rule `^lean/FramedChannel/Model/;^FramedChannel\.Composition\.` forbids any
`Model/` file from importing a composition. It goes here, beside
`Composition/StuffedChannel/`, file for file.

## `feed` is a `List.foldl`, and that is the whole cost model

`feed` folds the one-byte transition `step` over the fed bytes. Chunking invariance --
`feed (a ++ b) = feed (feed a) b`, the L1 field `ReceiverLaws.feed_append` -- is then
`List.foldl_append` and nothing more, and resync progress and order preservation follow from it in
two rewrites rather than needing inductions of their own. That is why the interface makes chunking
invariance a law and those two derived theorems.

The Rust `feed` is the same fold written as a `while` loop with an unconditional `i += 1`
(`rust/src/receiver.rs`), which is what makes its termination measure decrease on every branch, the
rejected run included.

## What a run carries across a `feed`, and what that costs

`buf` holds the bytes of the run currently being scanned, and they persist across calls. The
alternative -- discard an unterminated tail at the end of each `feed` -- makes chunking invariance
false and costs both derived theorems. The price is that a wire carrying no flag grows `buf`
without bound; `certificate/receiver.yaml`'s `not_claimed:` block records that standing limit with
a bounded-buffer variant named as future work.

An empty run is *idle*, not a drop: RFC 1662 §4.1 has two adjacent flags delimit an empty frame a
conforming receiver ignores, and `finishRun`'s early return on an empty buffer is what makes
`ReceiverLaws.idle_flags` statable at all. A full-queue refusal, by contrast, *is* a drop -- the
same conflation of two causes `Channel.DeliverFail` already makes -- which is what keeps
`run_exactly_one` unconditional at the cost of `feed_frame`'s `room` hypothesis.

Like the other composition-layer definitions, these see the queue only through `Spec/Queue.lean`:
this module imports no queue model.
-/

namespace FramedChannel.Receiver

open FramedChannel
open FramedChannel.Channel (Frame FrameOK FrameCarrier)

/-- The receiver state: the output queue of accepted frames, the bytes of the run currently being
scanned, and the number of runs dropped. Field for field `rust/src/receiver.rs`'s `Receiver<Q>`. -/
structure Rcv (Q : Type) where
  /-- The accepted frames, in a bounded queue reached only through `Spec/Queue.lean`. -/
  out : Q
  /-- The bytes of the run being scanned, flag-free by construction. -/
  buf : List Nat
  /-- The number of runs the receiver could not accept. -/
  dropped : Nat

section defs
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]

/-- The per-run acceptance test: terminate the run with one flag and hand it whole to
`StuffedChannel.parseStuffed`.

This is reuse, not a second parser. Because `buf` is flag-free by construction and exactly one flag
is appended, the codec's decode always stops at that appended flag, the run is consumed entire, and
`parseStuffed`'s own "nothing left over" check *is* the run's exactness check. There is nothing left
for a receiver-specific parser to do, and nothing to keep in step with the sender's. The Rust
`finish_run` is the same one-line reuse of `stuffed_channel::parse_stuffed`. -/
def acceptRun (flag : Nat) (r : List Nat) : Result (Frame × List Nat) :=
  StuffedChannel.parseStuffed (C := C) (K := K) (r ++ [flag])

/-- The sender's wire for `p`, decomposed as the run and its terminating flag: the shape `feed`
consumes, and the hypothesis `feed_frame` and its two derived theorems carry.

Stated as a hypothesis rather than derived from `Transparent`, and the reason is not
defensiveness. `Transparent` gives `ends_with_flag` and `body_flag_free`, so the encoding always
*has* this shape -- but it does not exclude an encoding equal to `[flag]` alone, whose run is
empty. `idle_flags` makes such a wire a no-op, so a `feed_frame` without `run ≠ []` would
contradict `idle_flags` rather than merely overclaim. At HDLC stuffing the run is non-empty and
`Composition/Receiver/Instances.lean` discharges it there. -/
def EncRun (flag : Nat) (p : Frame) (run : List Nat) : Prop :=
  StuffedChannel.encodeStuffed (C := C) (K := K) p = run ++ [flag] ∧ run ≠ []

variable {Q E : Type} [FrameCarrier E] [QueueModel Q E]

/-- A flag has arrived: judge the buffered run and clear it.

Three outcomes, and the Rust `finish_run` has the same three: an empty run is idle and the receiver
is untouched; a run the acceptance test takes is pushed onto the output queue; a run it rejects --
or one the queue refuses -- is one drop. -/
def finishRun (flag : Nat) (c : Rcv Q) : Rcv Q :=
  if c.buf.isEmpty then c
  else
    match acceptRun (C := C) (K := K) flag c.buf with
    | .ok (p, _) =>
      match QueueModel.push c.out (FrameCarrier.ofFrame (E := E) p) with
      | .ok q' => { out := q', buf := [], dropped := c.dropped }
      | .fail => { out := c.out, buf := [], dropped := c.dropped + 1 }
    | .fail => { out := c.out, buf := [], dropped := c.dropped + 1 }

/-- One byte off the wire: a flag ends the run, anything else extends it. Every branch is total,
which is the model-level reading of the Rust loop's unconditional advance. -/
def step (flag : Nat) (c : Rcv Q) (b : Nat) : Rcv Q :=
  if b = flag then finishRun (C := C) (K := K) (E := E) flag c
  else { c with buf := c.buf ++ [b] }

/-- `Receiver::feed`: arbitrary bytes off the wire, folded one byte at a time. Written as a
`List.foldl` so that chunking invariance is `List.foldl_append` -- see the module docstring. -/
def feed (flag : Nat) (c : Rcv Q) (w : List Nat) : Rcv Q :=
  w.foldl (step (C := C) (K := K) (E := E) flag) c

/-- `Receiver::poll`: take the oldest accepted frame off the output queue, or refuse. -/
def poll (c : Rcv Q) : Result (E × Rcv Q) :=
  match QueueModel.pop (Q := Q) (α := E) c.out with
  | .ok (x, q') => .ok (x, { c with out := q' })
  | .fail => .fail

/-- The accepted-frame observation, oldest first: the abstraction function every law is stated
over, as `QueueModel.toList` is for the queue. -/
def accepted (c : Rcv Q) : List E := QueueModel.toList (Q := Q) (α := E) c.out

/-- Whether the output queue can take one more frame: the `feed_frame` hypothesis. -/
def room (c : Rcv Q) : Bool := ! QueueModel.full (Q := Q) (α := E) c.out

/-- Whether the receiver is at a run boundary, with no partial run buffered. -/
def quiet (c : Rcv Q) : Bool := c.buf.isEmpty

/-! ## The canonical model as an instance of the L0 interface

`ReceiverModel` carries operations only, so its instance is a definition and belongs here rather
than in `Composition/Receiver/Instances.lean` -- `Model/VecQueue/Defs.lean` holds `instQueueModel`
for the same reason while `Model/VecQueue/Theorems.lean` holds `instBoundedQueueLaws`. It also has
to be here: `FramedChannelChallenge.Receiver` restates the registered `instReceiverLaws`, whose type
cannot elaborate without this instance, and a Challenge module may import a `Defs` module but not a
proof module. -/

/-- The canonical model's operations as an instance of the L0 interface: `Rcv Q` over any bounded
queue of frames, at HDLC byte stuffing and the bitwise CRC-8. -/
instance instReceiverModel {Q : Type} [QueueModel Q Frame] : ReceiverModel (Rcv Q) Frame where
  feed r w := feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker r w
  poll r := poll (Q := Q) (E := Frame) r
  accepted r := accepted (Q := Q) (E := Frame) r
  dropped r := r.dropped
  room r := room (Q := Q) (E := Frame) r
  quiet r := quiet (Q := Q) r

/-- The receiver invariant: the buffered run is flag-free. `feed` preserves it -- a byte equal to
the flag ends the run rather than entering it -- which is what lets the acceptance test terminate
the run with exactly one flag and rely on the codec stopping there. -/
def RcvInv (flag : Nat) (c : Rcv Q) : Prop := ∀ b ∈ c.buf, b ≠ flag

end defs

end FramedChannel.Receiver
