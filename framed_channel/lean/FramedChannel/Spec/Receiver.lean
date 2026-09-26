-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Result
import FramedChannel.Spec.Queue
import FramedChannel.Spec.Codec
import FramedChannel.Spec.Checksum

/-!
# Spec/Receiver: the resynchronizing-receiver interface, `ReceiverModel` (L0) and `ReceiverLaws` (L1)

The two-layer anatomy `Spec/Queue.lean` gives the queue, at a receive path that never wedges:
operations and types in `ReceiverModel`, laws over the accepted-frame observation in
`ReceiverLaws`. Every law here is stated through `accepted` and `dropped` -- never over a concrete
buffer or queue representation -- exactly as `BoundedQueueLaws` is stated through `toList`.

This is the second interface of the example whose operation shape fits none of `QueueModel`,
`CodecModel` or `ChecksumModel` (`Spec/Serial.lean` was the first). The shape is: feed a byte
stream, observe an accepted-frame sequence and a drop count. There is no encode/decode pair -- the
framing codec is a *component* this receiver composes, not what this interface is about -- and no
container: the accepted frames go into a queue the receiver reaches through `Spec/Queue.lean`.

## Four design decisions, each load-bearing

**`room` and `quiet` are L0 fields, because two laws have side conditions and a side condition must
be expressible at the interface.** `feed_frame` holds only when the output queue can take the
frame, and three laws hold only at a *run boundary* -- with no partial run buffered from an earlier
`feed`. Both conditions are about receiver state the laws are otherwise silent about, so each
enters L0 as one `Bool`-valued observation rather than being smuggled into the operations the laws
are about. `SerialModel.defined` is the existing precedent for exactly this move, and it is the
same argument: the alternative widens `feed` to hide its own hypothesis.

**There is no `init` field.** A receiver is created at a capacity (`Receiver::with_queue(capacity)`
in `rust/src/receiver.rs`), and `QueueModel` offers no empty-queue constructor, so a parameterless
`init : R` would be a field the canonical model cannot define and no law below could constrain --
the same vacuity `Spec/Serial.lean` rejects an `iter` field for. The laws quantify over every
receiver instead, with `quiet` naming the run-boundary states they need.

**Every field is `Bool`-valued or equation-shaped, or an explicit disjunction.** Every law is
therefore decidable at the canonical model, which is what keeps the kernel `decide` rung and the
kernel countermodel searches of `Evidence/Countermodels.lean` in reach. A `Prop`-valued `room` or
`quiet` would put both out of reach for the sake of notation.

**`flag`, `enc` and `Dom` are class *parameters*, not fields.** A `Prop`-valued class cannot carry
data fields; `Composition/StuffedChannel/Defs.lean`'s `Transparent` resolves the same constraint
the same way.

## What this interface deliberately does not require

**Resync progress and order preservation are not fields, and their absence is a derivation rather
than an omission.** `feed_append` -- chunking invariance, that what the receiver does is
independent of how the stream is cut up -- makes both follow in two rewrites: split the wire at the
garbage prefix's terminating flag, then apply `feed_frame` to the remainder. Both are proved as
derived theorems in `Composition/Receiver/Instances.lean`, whose docstrings say so. Registering
either as a seventh field would state twice what `feed_append` already gives once.

**Soundness is not a field either**, because its statement mentions the framing codec's `encode`:
it is a fact about how the receiver composes a *component*, not about the receiver's own operations,
and it is proved at the composition layer as `FramedChannel.Receiver.accepted_sound`.

**Nothing here bounds the buffered run.** A wire carrying no flag buffers without limit. That is a
recorded standing limit of the canonical model (`certificate/receiver.yaml`'s `not_claimed:`
block), not a law this interface withholds.

## The canonical model, so neither class is vacuous

`Composition/Receiver/Instances.lean`'s `instReceiverLaws` is an inhabited instance of both
classes: the `Rcv Q` of `Composition/Receiver/Defs.lean` over any lawful bounded queue, at HDLC
byte stuffing (`Stuff.Hdlc`), the bitwise CRC-8 (`Crc8.Bitwise`), `flag := Stuff.marker`,
`enc := StuffedChannel.encodeStuffed` and `Dom := Channel.FrameOK`. The instance is *not* here:
this module is specification only, and `check.sh`'s layer rule forbids a `Spec/` module from
importing a model or a composition. `Spec/Codec.lean` names `Leb128` the same way and for the same
reason, and `Spec/Serial.lean` names `SeqNum.instSerialLaws`.
-/

namespace FramedChannel

/-- L0: the operations of a resynchronizing receive path over a representation `R`, delivering
frames of type `F`. Operations and types only. -/
class ReceiverModel (R : Type) (F : Type) where
  /-- Feed bytes off the wire. Bytes buffer across calls, which is what `ReceiverLaws.feed_append`
  is about. -/
  feed : R → List Nat → R
  /-- Take the oldest accepted frame, or refuse. -/
  poll : R → Result (F × R)
  /-- The abstraction function: the accepted frames, oldest first. Every law below is stated over
  this observation. -/
  accepted : R → List F
  /-- The number of runs the receiver could not accept. -/
  dropped : R → Nat
  /-- Whether the receiver can take one more frame. The hypothesis of
  `ReceiverLaws.feed_frame`. -/
  room : R → Bool
  /-- Whether the receiver is at a run boundary, with no partial run buffered. The hypothesis of
  `ReceiverLaws.idle_flags`, `run_exactly_one` and `feed_frame`. -/
  quiet : R → Bool

/-- L1: the laws a resynchronizing receive path must satisfy, stated through `accepted` and
`dropped`.

`flag` is the byte that delimits a run, `enc` is how the sender encodes a frame, and `Dom` is the
frames the sender is claimed to encode correctly. Six fields; see the module docstring on why
resync progress, order preservation and soundness are derived rather than required. -/
class ReceiverLaws (R : Type) (F : Type) [ReceiverModel R F] (flag : Nat) (enc : F → List Nat)
    (Dom : F → Prop) : Prop where
  /-- `poll` agrees with the `accepted` observation: whatever it hands back is the frame that
  observation has at its front. Stated in this direction, rather than as "a non-empty observation
  can be polled", because that is the direction a client needs and the one `BoundedQueueLaws.pop_law`
  supports without a further emptiness law. -/
  poll_accepted : ∀ (r r' : R) (x : F), ReceiverModel.poll (R := R) (F := F) r = .ok (x, r') →
    ReceiverModel.accepted (R := R) (F := F) r
      = x :: ReceiverModel.accepted (R := R) (F := F) r'
  /-- Chunking invariance: what the receiver does is independent of how the stream is cut up. This
  is the field the two derived theorems rest on -- see the module docstring. -/
  feed_append : ∀ (r : R) (a b : List Nat),
    ReceiverModel.feed (R := R) (F := F) r (a ++ b)
      = ReceiverModel.feed (R := R) (F := F) (ReceiverModel.feed (R := R) (F := F) r a) b
  /-- Nothing is accepted and nothing is dropped before a flag arrives: until a run is terminated
  there is no run to judge. -/
  quiet_before_flag : ∀ (r : R) (w : List Nat), (∀ b ∈ w, b ≠ flag) →
    ReceiverModel.accepted (R := R) (F := F) (ReceiverModel.feed (R := R) (F := F) r w)
        = ReceiverModel.accepted (R := R) (F := F) r ∧
      ReceiverModel.dropped (R := R) (F := F) (ReceiverModel.feed (R := R) (F := F) r w)
        = ReceiverModel.dropped (R := R) (F := F) r
  /-- Flags alone are idle (RFC 1662 §4.1): from a run boundary, any number of adjacent flags
  delimit empty frames a conforming receiver ignores, so they are not drops. -/
  idle_flags : ∀ (r : R) (k : Nat), ReceiverModel.quiet (R := R) (F := F) r = true →
    ReceiverModel.feed (R := R) (F := F) r (List.replicate k flag) = r
  /-- Each non-empty flag-terminated run yields exactly one accepted frame or exactly one drop --
  never both and never neither -- and leaves the receiver at a run boundary again. The disjunction
  is explicit rather than an inequality on counts, so the law stays decidable. -/
  run_exactly_one : ∀ (r : R) (run : List Nat), run ≠ [] → (∀ b ∈ run, b ≠ flag) →
    ReceiverModel.quiet (R := R) (F := F) r = true →
    ReceiverModel.quiet (R := R) (F := F)
        (ReceiverModel.feed (R := R) (F := F) r (run ++ [flag])) = true ∧
      ((∃ x : F,
          ReceiverModel.accepted (R := R) (F := F)
              (ReceiverModel.feed (R := R) (F := F) r (run ++ [flag]))
            = ReceiverModel.accepted (R := R) (F := F) r ++ [x] ∧
          ReceiverModel.dropped (R := R) (F := F)
              (ReceiverModel.feed (R := R) (F := F) r (run ++ [flag]))
            = ReceiverModel.dropped (R := R) (F := F) r)
        ∨ (ReceiverModel.accepted (R := R) (F := F)
              (ReceiverModel.feed (R := R) (F := F) r (run ++ [flag]))
            = ReceiverModel.accepted (R := R) (F := F) r ∧
           ReceiverModel.dropped (R := R) (F := F)
              (ReceiverModel.feed (R := R) (F := F) r (run ++ [flag]))
            = ReceiverModel.dropped (R := R) (F := F) r + 1))
  /-- A well-formed frame's encoding is accepted, in order, with nothing dropped, and the receiver
  is left at a run boundary.

  The encoding is required to *be* a non-empty flag-free run terminated by the flag, as one
  decomposition hypothesis. That is not a defensive qualifier: without it the field contradicts
  `idle_flags`, since an `enc x` equal to `[flag]` alone is by `idle_flags` a no-op. At the
  canonical model the decomposition is forced by the composition-layer `Transparent` bundle's
  `body_flag_free` and `ends_with_flag`, which is the sense in which transparency is what makes
  this receive path sound at all. -/
  feed_frame : ∀ (r : R) (x : F) (run : List Nat), Dom x → enc x = run ++ [flag] → run ≠ [] →
    (∀ b ∈ run, b ≠ flag) → ReceiverModel.room (R := R) (F := F) r = true →
    ReceiverModel.quiet (R := R) (F := F) r = true →
    ReceiverModel.accepted (R := R) (F := F) (ReceiverModel.feed (R := R) (F := F) r (enc x))
        = ReceiverModel.accepted (R := R) (F := F) r ++ [x] ∧
      ReceiverModel.dropped (R := R) (F := F) (ReceiverModel.feed (R := R) (F := F) r (enc x))
        = ReceiverModel.dropped (R := R) (F := F) r ∧
      ReceiverModel.quiet (R := R) (F := F) (ReceiverModel.feed (R := R) (F := F) r (enc x)) = true

end FramedChannel
