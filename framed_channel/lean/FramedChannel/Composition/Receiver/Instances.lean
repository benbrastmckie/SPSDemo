-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Composition.Receiver.Theorems
import FramedChannel.Composition.StuffedChannel.Instances
import FramedChannel.Model.RingBuffer.Theorems
import FramedChannel.Model.VecQueue.Theorems

/-!
# Composition/Receiver/Instances: where the receive path's four interfaces meet their models

`Composition/Receiver/Theorems.lean` proves every theorem from `Spec/Queue.lean`,
`Spec/Codec.lean`'s L0 plus the composition-layer `Transparent` bundle, `Spec/Checksum.lean`'s L0,
and the new `Spec/Receiver.lean` -- and imports no queue model, no `Model/Stuff/Theorems` and no
`Model/Crc8/Theorems`. This module is where the composition layer meets the model layer, four times
over:

* `instReceiverModel` and `instReceiverLaws` show the new interface is **not vacuous**: the
  canonical model `Rcv Q`, over any lawful bounded queue of frames, at HDLC byte stuffing
  (`Stuff.Hdlc`), the bitwise CRC-8 (`Crc8.Bitwise`), `flag := Stuff.marker`,
  `enc := StuffedChannel.encodeStuffed` and `Dom := Channel.FrameOK`, satisfies all six L1 laws.
  `Spec/Receiver.lean`'s docstring names this instance, as `Spec/Codec.lean` names `Leb128` and
  `Spec/Serial.lean` names `SeqNum.instSerialLaws`; the layer rule keeps the instance out of
  `Spec/`;
* `encRun_hdlc` discharges the `EncRun` decomposition at HDLC stuffing, from
  `Stuff.stuff`'s own shape: a non-empty body stuffs to a non-empty run, so the wire is `run` plus
  one terminating flag with `run ≠ []`. That is the hypothesis `Composition/Receiver/Theorems.lean`
  cannot derive from `Transparent` alone, and the reason is recorded there;
* `resync_progress` and `order_preserved` are **derived**, not re-proved. Both are `feed_append`
  followed by `feed_frame`: chunking invariance splits the wire, and the frame law finishes.
  `resync_progress` is two rewrites; `order_preserved` is that same pair under one induction on the
  frame list. `Spec/Receiver.lean`'s docstring records why neither earns an L1 field, and `Zigzag`
  sets the precedent of recording a derived law as a theorem rather than a field;
* `feed_spec_RB` and `feed_spec_VQ` instantiate the one `feed_frame` proof at the ring buffer
  (`RingBuffer.BQ`) and at the list-backed queue (`VecQueue.VQ`) with no reproof. That is the
  substitution row `Receiver[VQ/BQ]`, the same row `Channel` and `StuffedChannel` exercise, now
  exercised at a receive path.

Both instantiations fix the checksum at `Crc8.Bitwise`, the digest the Rust `crc8` computes.

The declarations are in namespace `FramedChannel.Receiver`, beside the theorems they instantiate.
-/

namespace FramedChannel.Receiver

open FramedChannel
open FramedChannel.Channel (Frame FrameOK FrameCarrier)

/-! ## The `EncRun` decomposition at HDLC stuffing -/

section hdlc
variable {K : Type} [ChecksumModel K]

/-- Stuffing a non-empty payload yields a non-empty run: every byte contributes one or two bytes,
never none. A supporting lemma. `[PROVED: kernel]` -/
theorem stuff_ne_nil (l : List Nat) (h : l ≠ []) : Stuff.stuff l ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons b bs =>
    simp only [Stuff.stuff, Stuff.stuffByte]
    split
    · simp
    · split <;> simp

/-- A frame body is never empty: it carries at least a length byte and a check byte. A supporting
lemma. `[PROVED: kernel]` -/
theorem body_ne_nil (p : Frame) : StuffedChannel.body (K := K) p ≠ [] := by
  simp [StuffedChannel.body]

/-- The `EncRun` decomposition at HDLC stuffing: the wire a sender writes is a non-empty stuffed run
plus one terminating flag. This is what `Composition/Receiver/Theorems.lean` takes as a hypothesis
because `Transparent` does not give it -- see that module's docstring. A supporting lemma.
`[PROVED: kernel]` -/
theorem encRun_hdlc (p : Frame) :
    EncRun (C := Stuff.Hdlc) (K := K) Stuff.marker p
      (Stuff.stuff (StuffedChannel.body (K := K) p)) := by
  refine ⟨?_, stuff_ne_nil _ (body_ne_nil (K := K) p)⟩
  simp [StuffedChannel.encodeStuffed, CodecModel.encode, Stuff.encode]

end hdlc

/-! ## The canonical model as an instance of the new interface -/

section canonical
variable {Q : Type} [QueueModel Q Frame]

/-- The canonical model's operations as an instance of the new L0 interface. -/
instance instReceiverModel : ReceiverModel (Rcv Q) Frame where
  feed r w := feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker r w
  poll r := poll (Q := Q) (E := Frame) r
  accepted r := accepted (Q := Q) (E := Frame) r
  dropped r := r.dropped
  room r := room (Q := Q) (E := Frame) r
  quiet r := quiet (Q := Q) r

/-- The interface's `feed` is the model's own. A supporting lemma. `[PROVED: kernel]` -/
theorem model_feed (r : Rcv Q) (w : List Nat) :
    ReceiverModel.feed (R := Rcv Q) (F := Frame) r w
      = feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker r w := rfl

/-- `ReceiverModel.quiet` is the empty-buffer condition the model's theorems state. A supporting
lemma. `[PROVED: kernel]` -/
theorem model_quiet (r : Rcv Q) :
    (ReceiverModel.quiet (R := Rcv Q) (F := Frame) r = true) ↔ r.buf = [] := by
  simp [ReceiverModel.quiet, quiet]

/-- `ReceiverModel.room` is the not-full condition the model's theorems state. A supporting lemma.
`[PROVED: kernel]` -/
theorem model_room (r : Rcv Q) :
    (ReceiverModel.room (R := Rcv Q) (F := Frame) r = true) ↔
      QueueModel.full (Q := Q) (α := Frame) r.out = false := by
  simp [ReceiverModel.room, room]

end canonical

section laws
variable {Q : Type} [QueueModel Q Frame] [BoundedQueueLaws Q Frame]

/-- NON-VACUITY: the canonical model satisfies every L1 law of `Spec/Receiver.lean`, so neither
`ReceiverModel` nor `ReceiverLaws` is an empty class. Instantiated at `Stuff.Hdlc`, `Crc8.Bitwise`,
`Stuff.marker`, `StuffedChannel.encodeStuffed` and `Channel.FrameOK`, over any lawful bounded queue
of frames. `[PROVED: kernel]` -/
instance instReceiverLaws :
    ReceiverLaws (Rcv Q) Frame Stuff.marker
      (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise)) FrameOK where
  poll_accepted r r' x h := poll_ok_accepted (Q := Q) (E := Frame) r r' x h
  feed_append r a b := feed_append (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
    r Stuff.marker a b
  quiet_before_flag r w hw := quiet_before_flag (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
    r Stuff.marker w hw
  idle_flags r k hq := idle_flags (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
    r Stuff.marker k ((model_quiet r).mp hq)
  run_exactly_one r run hne hfree hq := by
    have h := run_exactly_one (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
      r Stuff.marker run hne hfree ((model_quiet r).mp hq)
    exact ⟨(model_quiet _).mpr h.1, h.2⟩
  feed_frame r x run hx heq hne hfree hroom hq := by
    have h := feed_frame (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
      r Stuff.marker x run hx ⟨heq, hne⟩ ((model_room r).mp hroom) ((model_quiet r).mp hq)
    exact ⟨h.1, h.2.1, (model_quiet _).mpr h.2.2⟩

ladder_record% instReceiverLaws instance

end laws

/-! ## The two derived theorems -/

section terminated
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]
variable {Q E : Type} [FrameCarrier E] [QueueModel Q E]

/-- A flag-terminated wire always leaves the receiver at a run boundary, whatever it was doing
before: every branch of `finishRun` clears the buffer. This is what lets `resync_progress` apply
`feed_frame` to the remainder without a hypothesis about `c`. A supporting lemma.
`[PROVED: kernel]` -/
theorem feed_terminated_buf (flag : Nat) (c : Rcv Q) (w : List Nat) :
    (feed (C := C) (K := K) (E := E) flag c (w ++ [flag])).buf = [] := by
  rw [feed_append, feed_cons, feed_nil]
  simp only [step, if_true]
  exact finishRun_buf (C := C) (K := K) (E := E) flag _

end terminated

section derivedCanonical
variable {Q : Type} [QueueModel Q Frame] [BoundedQueueLaws Q Frame]

local notation "FEED" => feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker
local notation "ENC" => StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise)
local notation "ACC" => accepted (Q := Q) (E := Frame)

/-- At `E := Frame` the frame carrier is the identity. A supporting lemma. `[PROVED: kernel]` -/
theorem ofFrame_id (p : Frame) : FrameCarrier.ofFrame (E := Frame) p = p := rfl

/-- RESYNC PROGRESS, DERIVED: a well-formed frame preceded by an arbitrary garbage prefix is
accepted, once that prefix is terminated by a flag.

Two rewrites: `feed_append` splits the wire at the prefix's terminating flag, and `feed_frame`
finishes. Nothing about runs or buffers is re-derived, which is the point of making chunking
invariance the law and this a theorem (`Spec/Receiver.lean`'s docstring records why).

The prefix must be FLAG-TERMINATED. An unterminated prefix fuses with the following frame's body
and that frame is lost -- `quiet_before_flag` is the positive statement of the same fact, and
`rust/tests/differential.rs`'s `receiver_resyncs` executes both halves. No run-boundary hypothesis
on `c` is needed: the prefix's own terminating flag establishes the boundary. `[PROVED: kernel]` -/
theorem resync_progress (c : Rcv Q) (g : List Nat) (p : Frame) (hp : FrameOK p)
    (hroom : QueueModel.full (Q := Q) (α := Frame) (FEED c (g ++ [Stuff.marker])).out = false) :
    ACC (FEED c (g ++ [Stuff.marker] ++ ENC p)) = ACC (FEED c (g ++ [Stuff.marker])) ++ [p] := by
  rung manual =>
    rw [feed_append]
    exact (feed_frame (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
      (FEED c (g ++ [Stuff.marker])) Stuff.marker p _ hp (encRun_hdlc p) hroom
      (feed_terminated_buf (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c g)).1

/-- The accumulating form `order_preserved` is the induction of. A supporting lemma.
`[PROVED: kernel]` -/
theorem order_preserved_aux (ps : List Frame) : ∀ c : Rcv Q, (∀ p ∈ ps, FrameOK p) → c.buf = [] →
    (∀ k, k < ps.length →
      QueueModel.full (Q := Q) (α := Frame) (FEED c (((ps.take k).map ENC).flatten)).out = false) →
    ACC (FEED c ((ps.map ENC).flatten)) = ACC c ++ ps ∧
      (FEED c ((ps.map ENC).flatten)).dropped = c.dropped ∧
      (FEED c ((ps.map ENC).flatten)).buf = [] := by
  induction ps with
  | nil => intro c _ hbuf _; simpa [feed_nil] using hbuf
  | cons p t ih =>
    intro c hps hbuf hroom
    have hp : FrameOK p := hps p (by simp)
    have ht : ∀ x ∈ t, FrameOK x := fun x hx => hps x (by simp [hx])
    have hr0 : QueueModel.full (Q := Q) (α := Frame) c.out = false := by
      have := hroom 0 (by simp)
      simpa [feed_nil] using this
    have hstep := feed_frame (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
      c Stuff.marker p _ hp (encRun_hdlc p) hr0 hbuf
    have hflat : ((p :: t).map ENC).flatten = ENC p ++ ((t.map ENC).flatten) := by simp
    rw [hflat, feed_append]
    have hroom' : ∀ k, k < t.length →
        QueueModel.full (Q := Q) (α := Frame)
          (FEED (FEED c (ENC p)) (((t.take k).map ENC).flatten)).out = false := by
      intro k hk
      have := hroom (k + 1) (by simpa using hk)
      rwa [show ((p :: t).take (k + 1)).map ENC = ENC p :: (t.take k).map ENC by simp,
        show (ENC p :: (t.take k).map ENC).flatten = ENC p ++ (((t.take k).map ENC).flatten) by simp,
        feed_append] at this
    obtain ⟨ha, hd, hb⟩ := ih (FEED c (ENC p)) ht hstep.2.2 hroom'
    refine ⟨?_, ?_, hb⟩
    · rw [ha, hstep.1]; simp [ofFrame_id]
    · rw [hd, hstep.2.1]

/-- ORDER PRESERVATION, DERIVED: a clean stream of well-formed frames is accepted in order, with
none lost and nothing dropped. One induction on the frame list over `feed_append` and `feed_frame`.

The room condition is stated per prefix rather than as a capacity sum, because `BoundedQueueLaws`
supports no capacity arithmetic over a list of pushes -- it constrains `push` one element at a time
through `toList`. `[PROVED: kernel]` -/
theorem order_preserved (c : Rcv Q) (ps : List Frame) (hps : ∀ p ∈ ps, FrameOK p)
    (hbuf : c.buf = []) (hempty : ACC c = [])
    (hroom : ∀ k, k < ps.length →
      QueueModel.full (Q := Q) (α := Frame) (FEED c (((ps.take k).map ENC).flatten)).out = false) :
    ACC (FEED c ((ps.map ENC).flatten)) = ps ∧
      (FEED c ((ps.map ENC).flatten)).dropped = c.dropped := by
  rung manual =>
    obtain ⟨ha, hd, _⟩ := order_preserved_aux ps c hps hbuf hroom
    exact ⟨by rw [ha, hempty]; simp, hd⟩

end derivedCanonical

/-! ## The substitution row: one proof at both queue models -/

section substitution

/-- `feed_frame` at the ring buffer, HDLC framing, bitwise CRC-8. `[PROVED: kernel]` -/
theorem feed_spec_RB (c : Rcv (RingBuffer.BQ Frame)) (p : Frame) (hp : FrameOK p)
    (hroom : QueueModel.full (Q := RingBuffer.BQ Frame) (α := Frame) c.out = false)
    (hbuf : c.buf = []) :
    (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise) p)).out.1.contents
      = c.out.1.contents ++ [p] ∧
    (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise) p)).dropped
      = c.dropped := by
  rung manual =>
    have h := feed_frame (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
      c Stuff.marker p _ hp (encRun_hdlc p) hroom hbuf
    exact ⟨by simpa [accepted, QueueModel.toList, ofFrame_id] using h.1, h.2.1⟩

/-- The same proof at the list-backed queue, with no reproof. `[PROVED: kernel]` -/
theorem feed_spec_VQ (c : Rcv (VecQueue.VQ Frame)) (p : Frame) (hp : FrameOK p)
    (hroom : QueueModel.full (Q := VecQueue.VQ Frame) (α := Frame) c.out = false)
    (hbuf : c.buf = []) :
    (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise) p)).out.items
      = c.out.items ++ [p] ∧
    (feed (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) Stuff.marker c
        (StuffedChannel.encodeStuffed (C := Stuff.Hdlc) (K := Crc8.Bitwise) p)).dropped
      = c.dropped := by
  rung manual =>
    have h := feed_frame (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame)
      c Stuff.marker p _ hp (encRun_hdlc p) hroom hbuf
    exact ⟨by simpa [accepted, QueueModel.toList, ofFrame_id] using h.1, h.2.1⟩

end substitution

#print axioms instReceiverModel
#print axioms instReceiverLaws
#print axioms resync_progress
#print axioms order_preserved
#print axioms feed_spec_RB
#print axioms feed_spec_VQ

end FramedChannel.Receiver
