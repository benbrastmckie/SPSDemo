-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Receiver
import FramedChannel.Composition.Receiver.Defs
import FramedChannel.Model.Stuff.Defs
import FramedChannel.Model.Crc8.Defs
import FramedChannel.Model.RingBuffer.Defs
import FramedChannel.Model.VecQueue.Defs

/-!
# FramedChannelChallenge.Receiver: approved statements (resynchronizing receive path)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Composition/Receiver/Theorems.lean` and
`Composition/Receiver/Instances.lean`. See `lean/FramedChannelChallenge.lean` for what a Challenge
module is and what the gate checks.

`instReceiverLaws` is admissible here because `ReceiverLaws` is `Prop`-valued: a Challenge module may
hold no non-`Prop` instance, exactly as `FramedChannelChallenge.StuffedChannel`'s
`instTransparentHdlc` is admissible. Its L0 companion `instReceiverModel` is *not* restated here: it
carries operations rather than laws, so it is a definition, it lives in
`Composition/Receiver/Defs.lean`, and this module imports it rather than repeating it.
-/

namespace FramedChannel.Receiver
open FramedChannel
open FramedChannel.Channel (Frame FrameOK FrameCarrier)

section push
variable {Q E : Type} [QueueModel Q E] [BoundedQueueLaws Q E]

/-- `poll` on a non-empty queue succeeds and hands back the front of the `accepted` observation, as
`BoundedQueueLaws.pop_law` is stated through `toList`. -/
theorem poll_accepted (c : Rcv Q) (h : QueueModel.empty (Q := Q) (α := E) c.out = false) :
    ∃ (x : E) (c' : Rcv Q), poll (Q := Q) (E := E) c = .ok (x, c') ∧
      accepted (Q := Q) (E := E) c = x :: accepted (Q := Q) (E := E) c' := sorry

end push

section fold
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]
variable {Q E : Type} [FrameCarrier E] [QueueModel Q E]

/-- CHUNKING INVARIANCE: what the receiver does is independent of how the stream is cut up. This is
the law `resync_progress` and `order_preserved` are derived from. -/
theorem feed_append (c : Rcv Q) (flag : Nat) (a b : List Nat) :
    feed (C := C) (K := K) (E := E) flag c (a ++ b)
      = feed (C := C) (K := K) (E := E) flag
          (feed (C := C) (K := K) (E := E) flag c a) b := sorry

/-- Nothing is accepted and nothing is dropped before a flag arrives: until a run is terminated there
is no run to judge. -/
theorem quiet_before_flag (c : Rcv Q) (flag : Nat) (w : List Nat) (hw : ∀ b ∈ w, b ≠ flag) :
    accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c w)
        = accepted (Q := Q) (E := E) c ∧
      (feed (C := C) (K := K) (E := E) flag c w).dropped = c.dropped := sorry

/-- Flags alone are idle (RFC 1662 §4.1): from a run boundary, any number of adjacent flags delimit
empty frames a conforming receiver ignores, so they are not drops. -/
theorem idle_flags (c : Rcv Q) (flag : Nat) (k : Nat) (hbuf : c.buf = []) :
    feed (C := C) (K := K) (E := E) flag c (List.replicate k flag) = c := sorry

end fold

section runs
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]
variable {Q E : Type} [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]

/-- Each non-empty flag-terminated run yields exactly one accepted frame or exactly one drop -- never
both and never neither -- and leaves the receiver at a run boundary again. -/
theorem run_exactly_one (c : Rcv Q) (flag : Nat) (run : List Nat)
    (hne : run ≠ []) (hfree : ∀ b ∈ run, b ≠ flag) (hbuf : c.buf = []) :
    (feed (C := C) (K := K) (E := E) flag c (run ++ [flag])).buf = [] ∧
    ((∃ x : E,
        accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c (run ++ [flag]))
            = accepted (Q := Q) (E := E) c ++ [x] ∧
          (feed (C := C) (K := K) (E := E) flag c (run ++ [flag])).dropped = c.dropped)
      ∨ (accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c (run ++ [flag]))
            = accepted (Q := Q) (E := E) c ∧
         (feed (C := C) (K := K) (E := E) flag c (run ++ [flag])).dropped = c.dropped + 1)) := sorry

/-- A well-formed frame's encoding is accepted, in order, with nothing dropped, and the receiver is
left at a run boundary. The `EncRun` hypothesis is why this does not contradict `idle_flags`. -/
theorem feed_frame (c : Rcv Q) (flag : Nat) [StuffedChannel.Transparent C flag] (p : Frame)
    (run : List Nat) (hp : FrameOK p) (hrun : EncRun (C := C) (K := K) flag p run)
    (hroom : QueueModel.full (Q := Q) (α := E) c.out = false) (hbuf : c.buf = []) :
    accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c
          (StuffedChannel.encodeStuffed (C := C) (K := K) p))
        = accepted (Q := Q) (E := E) c ++ [FrameCarrier.ofFrame (E := E) p] ∧
      (feed (C := C) (K := K) (E := E) flag c
          (StuffedChannel.encodeStuffed (C := C) (K := K) p)).dropped = c.dropped ∧
      (feed (C := C) (K := K) (E := E) flag c
          (StuffedChannel.encodeStuffed (C := C) (K := K) p)).buf = [] := sorry

/-- SOUNDNESS: every frame a fresh receiver accepts off an arbitrary byte stream is the acceptance
test's own reading of a non-empty, flag-free, flag-terminated run that occurs in that stream. No
frame is invented out of corruption. -/
theorem accepted_sound (c : Rcv Q) (flag : Nat) (w : List Nat) (hbuf : c.buf = [])
    (hempty : accepted (Q := Q) (E := E) c = []) :
    ∀ x ∈ accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c w),
      ∃ (pre run suf : List Nat) (p : Frame) (rest : List Nat),
        w = pre ++ (run ++ [flag]) ++ suf ∧ (∀ b ∈ run, b ≠ flag) ∧ run ≠ [] ∧
          acceptRun (C := C) (K := K) flag run = .ok (p, rest) ∧
          x = FrameCarrier.ofFrame (E := E) p := sorry

end runs

section laws

/-- NON-VACUITY: the canonical model satisfies every L1 law of `Spec/Receiver.lean`, so neither
`ReceiverModel` nor `ReceiverLaws` is an empty class.

The two queue binders are written out rather than taken from a `variable` line: a `:= sorry` body
mentions neither, so section-variable inclusion would drop `BoundedQueueLaws` and the statement hash
would stop matching the registry's. -/
instance instReceiverLaws {Q : Type} [QueueModel Q Frame] [BoundedQueueLaws Q Frame] :
    ReceiverLaws (Rcv Q) Frame Stuff.marker
      (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise)) FrameOK := sorry

end laws

section derivedCanonical
variable {Q : Type} [QueueModel Q Frame] [BoundedQueueLaws Q Frame]

-- No `local notation` abbreviations here, although `Composition/Receiver/Instances.lean` uses them
-- for the same statements: a notation declaration elaborates to auxiliary `def`s, and the Lean
-- purity check (`FramedChannel/SpecCheck.lean`) counts every non-`sorry` declaration in a Challenge
-- module as IMPURE. The statements are therefore written out.

/-- RESYNC PROGRESS, DERIVED: a well-formed frame preceded by an arbitrary garbage prefix is
accepted, once that prefix is terminated by a flag. -/
theorem resync_progress (c : Rcv Q) (g : List Nat) (p : Frame) (hp : FrameOK p)
    (hroom : QueueModel.full (Q := Q) (α := Frame)
      (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (g ++ [Stuff.marker])).out = false) :
    accepted (Q := Q) (E := Frame)
        (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
          (g ++ [Stuff.marker] ++ StuffedChannel.encodeStuffed (C := Stuff.Hdlc)
            (K := Crc8.Bitwise) p))
      = accepted (Q := Q) (E := Frame)
          (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
            (g ++ [Stuff.marker])) ++ [p] := sorry

/-- ORDER PRESERVATION, DERIVED: a clean stream of well-formed frames is accepted in order, with
none lost and nothing dropped. -/
theorem order_preserved (c : Rcv Q) (ps : List Frame) (hps : ∀ p ∈ ps, FrameOK p)
    (hbuf : c.buf = [])
    (hempty : accepted (Q := Q) (E := Frame) c = [])
    (hroom : ∀ k, k < ps.length →
      QueueModel.full (Q := Q) (α := Frame)
        (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
          (((ps.take k).map (StuffedChannel.encodeStuffed (C := Stuff.Hdlc)
            (K := Crc8.Bitwise))).flatten)).out = false) :
    accepted (Q := Q) (E := Frame)
        (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
          ((ps.map (StuffedChannel.encodeStuffed (C := Stuff.Hdlc)
            (K := Crc8.Bitwise))).flatten)) = ps ∧
      (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        ((ps.map (StuffedChannel.encodeStuffed (C := Stuff.Hdlc)
          (K := Crc8.Bitwise))).flatten)).dropped = c.dropped := sorry

end derivedCanonical

section substitution

/-- `feed_frame` at the ring buffer, HDLC framing, bitwise CRC-8. -/
theorem feed_spec_RB (c : Rcv (RingBuffer.BQ Frame)) (p : Frame) (hp : FrameOK p)
    (hroom : QueueModel.full (Q := RingBuffer.BQ Frame) (α := Frame) c.out = false)
    (hbuf : c.buf = []) :
    (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise) p)).out.1.contents
      = c.out.1.contents ++ [p] ∧
    (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise) p)).dropped
      = c.dropped := sorry

/-- The same proof at the list-backed queue, with no reproof. -/
theorem feed_spec_VQ (c : Rcv (VecQueue.VQ Frame)) (p : Frame) (hp : FrameOK p)
    (hroom : QueueModel.full (Q := VecQueue.VQ Frame) (α := Frame) c.out = false)
    (hbuf : c.buf = []) :
    (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise) p)).out.items
      = c.out.items ++ [p] ∧
    (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise) p)).dropped
      = c.dropped := sorry

end substitution

end FramedChannel.Receiver
