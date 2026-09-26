-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Composition.Receiver.Defs
import FramedChannel.Composition.StuffedChannel.Theorems

/-!
# Composition/Receiver/Theorems: the resynchronizing receive path, proved from four interfaces

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/receiver.rs`. `feed` takes
arbitrary bytes off the wire one at a time, a flag ends the run being scanned, and the run is either
accepted as a frame or dropped and counted; `poll` hands back the oldest accepted frame. The Rust
`feed` and `poll` are the same two operations with the same three-way run judgement, so this is a
model of that file at the operation level.

## The theorem `StuffedChannel.deliver` cannot have

`accepted_sound`: every frame the receiver accepts is the acceptance test's own reading of a
non-empty, flag-free, flag-terminated run that actually occurs in the bytes fed. A receiver that
accepts arbitrary bytes invents nothing out of corruption. `deliver` has no counterpart, because it
reads only a wire its own `send` wrote and fails as a unit the moment that wire is malformed.

Soundness is stated with the witnessing **run** made explicit rather than as "the accepted frame's
own encoding occurs in the wire". The second form is FALSE, and
`Evidence/Countermodels.lean` refutes it in the kernel at the wire `[129, 0, 0, 0, 126]`: LEB128
length prefixes are not canonical (`Varint.decode [0x81, 0x00] = .ok (1, [])` while
`Varint.encode 1 = [1]`), so the receiver accepts `[0x00]` whose canonical encoding occurs nowhere
in the bytes that produced it. The run form is the stronger statement anyway, and it needs no
assumption that the framing codec distributes over `++`. The payload-and-check form follows from it
at HDLC stuffing, where `Stuff.stuff` is a per-byte homomorphism.

`Evidence/Countermodels.lean` refutes the second, more basic claim too: that a receiver scanning to
the next flag is sound over **unstuffed** `Channel` framing. It is not -- a payload byte equal to
the flag opens a run that happens to parse -- which is why this unit's acceptance test is
`StuffedChannel.parseStuffed` and why the composition-layer `Transparent` bundle's `body_flag_free`
is the load-bearing hypothesis of `feed_frame` rather than a decorative lemma.

## Composition: four interfaces, reached generically

* the output queue through `Spec/Queue.lean` alone (`QueueModel`, `BoundedQueueLaws`);
* the framing codec through `Spec/Codec.lean`'s L0 `CodecModel` plus the composition-layer bundle
  `Transparent` of `Composition/StuffedChannel/Defs.lean` -- **not** `CodecLaws`, for the two
  reasons that module's docstring records;
* the checksum through `Spec/Checksum.lean`'s L0 `ChecksumModel`. No `ChecksumLaws` law is used;
* the receive path itself through the **new** `Spec/Receiver.lean`, whose L1 `ReceiverLaws` this
  unit instantiates in `Composition/Receiver/Instances.lean`.

The per-run acceptance test is `StuffedChannel.parseStuffed` reused whole, not a second parser: see
`Composition/Receiver/Defs.lean`'s `acceptRun`.

## Why `feed_frame` carries a run decomposition

`EncRun flag p run` -- that the sender's wire for `p` is `run ++ [flag]` with `run` non-empty -- is
a hypothesis rather than a consequence of `Transparent`. `Transparent` gives `ends_with_flag` and
`body_flag_free`, so the wire always has that shape, but it does not exclude an encoding equal to
`[flag]` alone, whose run is empty. `idle_flags` makes such a wire a no-op, so a `feed_frame`
without `run ≠ []` would **contradict** `idle_flags` rather than merely overclaim.
`Composition/Receiver/Instances.lean` discharges `EncRun` at HDLC stuffing, where a non-empty body
stuffs to a non-empty run.

## Scope

* This module imports no queue model, so the genericity claim is mechanically visible; the
  instantiations at `RingBuffer.BQ` and `VecQueue.VQ` live in
  `Composition/Receiver/Instances.lean`, which is where the composition layer meets the model layer.
* `resync_progress` and `order_preserved` are **not** here. They are derived from `feed_append` and
  `feed_frame` in `Composition/Receiver/Instances.lean`, and `Spec/Receiver.lean`'s docstring
  records why they earn no law field of their own.
* `toList_push_ok`, `feed_nil`, `feed_cons`, `finishRun_buf`, `feed_flag_free`, `feed_run_eq`,
  `encRun_flag_free`, `poll_ok_accepted` and `feed_sound` are supporting lemmas, not registered
  rows -- `StuffedChannel` does not register its `send_out` analogue either.
* Nothing here bounds the buffered run: a wire carrying no flag buffers without limit.
  `certificate/receiver.yaml`'s `not_claimed:` block records that standing limit.
* Error agreement against the extracted code is a bridge-level obligation, discharged in
  `aeneas/FramedChannelAeneas/Bridge/Receiver/`.
-/

namespace FramedChannel.Receiver

open FramedChannel
open FramedChannel.Channel (Frame FrameOK FrameCarrier)

/-! ## The queue lemma every acceptance branch needs -/

section push
variable {Q E : Type} [QueueModel Q E] [BoundedQueueLaws Q E]

/-- A successful `push` appends exactly the element pushed. `BoundedQueueLaws.push_law` gives this
only under `¬ full`, and `full_law` is what turns a successful push into that hypothesis. A
supporting lemma. `[PROVED: kernel]` -/
theorem toList_push_ok (q : Q) (x : E) (q' : Q) (h : QueueModel.push q x = .ok q') :
    QueueModel.toList (Q := Q) (α := E) q'
      = QueueModel.toList (Q := Q) (α := E) q ++ [x] := by
  by_cases hf : QueueModel.full (Q := Q) (α := E) q
  · rw [BoundedQueueLaws.full_law q x hf] at h; exact absurd h (by simp)
  · obtain ⟨q'', hq'', htl⟩ := BoundedQueueLaws.push_law q x hf
    rw [hq''] at h
    simp only [Result.ok.injEq] at h
    subst h
    exact htl

/-- `poll` on a non-empty queue succeeds and hands back the front of the `accepted` observation, as
`BoundedQueueLaws.pop_law` is stated through `toList`. `[PROVED: kernel]` -/
theorem poll_accepted (c : Rcv Q) (h : QueueModel.empty (Q := Q) (α := E) c.out = false) :
    ∃ (x : E) (c' : Rcv Q), poll (Q := Q) (E := E) c = .ok (x, c') ∧
      accepted (Q := Q) (E := E) c = x :: accepted (Q := Q) (E := E) c' := by
  rung manual =>
    have hne : ¬ QueueModel.empty (Q := Q) (α := E) c.out := by simp [h]
    obtain ⟨x, q', hpop, htl⟩ := BoundedQueueLaws.pop_law c.out hne
    refine ⟨x, { c with out := q' }, ?_, ?_⟩
    · unfold poll; rw [hpop]
    · simpa [accepted] using htl

/-- The direction `Spec/Receiver.lean`'s `ReceiverLaws.poll_accepted` states: whatever `poll` hands
back is the front of the observation. Stated this way at the interface because `BoundedQueueLaws`
carries no law taking `toList q ≠ []` to `¬ empty q`, so the non-empty-observation direction is not
available there. A supporting lemma. `[PROVED: kernel]` -/
theorem poll_ok_accepted (c c' : Rcv Q) (x : E) (h : poll (Q := Q) (E := E) c = .ok (x, c')) :
    accepted (Q := Q) (E := E) c = x :: accepted (Q := Q) (E := E) c' := by
  unfold poll at h
  split at h
  · next y q'' hpop =>
    have hne : ¬ QueueModel.empty (Q := Q) (α := E) c.out := by
      intro hemp
      rw [BoundedQueueLaws.empty_law c.out hemp] at hpop
      exact absurd hpop (by simp)
    obtain ⟨z, q₀, hpop₀, htl⟩ := BoundedQueueLaws.pop_law c.out hne
    rw [hpop₀] at hpop
    simp only [Result.ok.injEq, Prod.mk.injEq] at hpop h
    obtain ⟨hz, hq⟩ := hpop
    subst hz; subst hq
    obtain ⟨hx, hc⟩ := h
    subst hx; subst hc
    simpa [accepted] using htl
  · next => exact absurd h (by simp)

end push

/-! ## `feed` as a fold, and what a flag-free stretch does -/

section fold
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]
variable {Q E : Type} [FrameCarrier E] [QueueModel Q E]

/-- Feeding nothing changes nothing. A supporting lemma. `[PROVED: kernel]` -/
theorem feed_nil (flag : Nat) (c : Rcv Q) :
    feed (C := C) (K := K) (E := E) flag c [] = c := rfl

/-- One byte off the front. A supporting lemma. `[PROVED: kernel]` -/
theorem feed_cons (flag : Nat) (c : Rcv Q) (b : Nat) (w : List Nat) :
    feed (C := C) (K := K) (E := E) flag c (b :: w)
      = feed (C := C) (K := K) (E := E) flag (step (C := C) (K := K) (E := E) flag c b) w := rfl

/-- CHUNKING INVARIANCE: what the receiver does is independent of how the stream is cut up. This is
the law `resync_progress` and `order_preserved` are derived from, and it is `List.foldl_append` and
nothing more -- which is why `feed` is written as a fold. `[PROVED: kernel]` -/
theorem feed_append (c : Rcv Q) (flag : Nat) (a b : List Nat) :
    feed (C := C) (K := K) (E := E) flag c (a ++ b)
      = feed (C := C) (K := K) (E := E) flag
          (feed (C := C) (K := K) (E := E) flag c a) b := by
  rung simp =>
    simp [feed]

/-- A run boundary is always reached after a flag: every branch of `finishRun` clears the buffer, and
the idle branch found it clear already. A supporting lemma. `[PROVED: kernel]` -/
theorem finishRun_buf (flag : Nat) (c : Rcv Q) :
    (finishRun (C := C) (K := K) (E := E) flag c).buf = [] := by
  unfold finishRun
  split
  · next h => simpa using List.isEmpty_iff.mp h
  · split
    · split <;> rfl
    · rfl

/-- A flag-free stretch of wire only extends the run being scanned. A supporting lemma.
`[PROVED: kernel]` -/
theorem feed_flag_free (flag : Nat) (c : Rcv Q) (w : List Nat) (hw : ∀ b ∈ w, b ≠ flag) :
    feed (C := C) (K := K) (E := E) flag c w = { c with buf := c.buf ++ w } := by
  induction w generalizing c with
  | nil => simp [feed_nil]
  | cons b t ih =>
    have hb : b ≠ flag := hw b (by simp)
    have ht : ∀ x ∈ t, x ≠ flag := fun x hx => hw x (by simp [hx])
    rw [feed_cons]
    have hstep : step (C := C) (K := K) (E := E) flag c b = { c with buf := c.buf ++ [b] } := by
      simp [step, hb]
    rw [hstep, ih _ ht]
    simp

/-- Feeding a flag-free run and its terminating flag, from a run boundary, is exactly `finishRun` on
that run. The structural lemma the three run-level theorems below share. A supporting lemma.
`[PROVED: kernel]` -/
theorem feed_run_eq (flag : Nat) (c : Rcv Q) (run : List Nat)
    (hfree : ∀ b ∈ run, b ≠ flag) (hbuf : c.buf = []) :
    feed (C := C) (K := K) (E := E) flag c (run ++ [flag])
      = finishRun (C := C) (K := K) (E := E) flag { c with buf := run } := by
  rw [feed_append, feed_flag_free (C := C) (K := K) (E := E) flag c run hfree, hbuf]
  simp only [List.nil_append]
  rw [feed_cons, feed_nil]
  simp [step]

/-- Nothing is accepted and nothing is dropped before a flag arrives: until a run is terminated there
is no run to judge. This is the qualifier `resync_progress` carries -- an unterminated garbage prefix
fuses with the following frame's body and that frame is lost. `[PROVED: kernel]` -/
theorem quiet_before_flag (c : Rcv Q) (flag : Nat) (w : List Nat) (hw : ∀ b ∈ w, b ≠ flag) :
    accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c w)
        = accepted (Q := Q) (E := E) c ∧
      (feed (C := C) (K := K) (E := E) flag c w).dropped = c.dropped := by
  rung manual =>
    rw [feed_flag_free (C := C) (K := K) (E := E) flag c w hw]
    exact ⟨rfl, rfl⟩

/-- Flags alone are idle (RFC 1662 §4.1): from a run boundary, any number of adjacent flags delimit
empty frames a conforming receiver ignores, so they are not drops. `finishRun`'s early return on an
empty buffer is what makes this statable. `[PROVED: kernel]` -/
theorem idle_flags (c : Rcv Q) (flag : Nat) (k : Nat) (hbuf : c.buf = []) :
    feed (C := C) (K := K) (E := E) flag c (List.replicate k flag) = c := by
  rung manual =>
    induction k with
    | zero => simp [feed_nil]
    | succ n ih =>
      rw [List.replicate_succ, feed_cons]
      have hstep : step (C := C) (K := K) (E := E) flag c flag = c := by
        simp [step, finishRun, hbuf]
      rw [hstep]
      exact ih

end fold

/-! ## The run-level theorems, where the queue laws enter -/

section runs
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]
variable {Q E : Type} [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]

/-- Each non-empty flag-terminated run yields exactly one accepted frame or exactly one drop -- never
both and never neither -- and leaves the receiver at a run boundary again. Unconditional: a
full-queue refusal is counted as a drop rather than excluded by a hypothesis, which is the same
conflation of two causes `Channel.DeliverFail` already makes. `[PROVED: kernel]` -/
theorem run_exactly_one (c : Rcv Q) (flag : Nat) (run : List Nat)
    (hne : run ≠ []) (hfree : ∀ b ∈ run, b ≠ flag) (hbuf : c.buf = []) :
    (feed (C := C) (K := K) (E := E) flag c (run ++ [flag])).buf = [] ∧
    ((∃ x : E,
        accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c (run ++ [flag]))
            = accepted (Q := Q) (E := E) c ++ [x] ∧
          (feed (C := C) (K := K) (E := E) flag c (run ++ [flag])).dropped = c.dropped)
      ∨ (accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c (run ++ [flag]))
            = accepted (Q := Q) (E := E) c ∧
         (feed (C := C) (K := K) (E := E) flag c (run ++ [flag])).dropped = c.dropped + 1)) := by
  rung manual =>
    rw [feed_run_eq (C := C) (K := K) (E := E) flag c run hfree hbuf]
    refine ⟨finishRun_buf (C := C) (K := K) (E := E) flag _, ?_⟩
    have hb : ({ c with buf := run } : Rcv Q).buf.isEmpty = false := by
      simpa using hne
    unfold finishRun
    rw [if_neg (by simp [hb])]
    split
    · next p rest hpr =>
      split
      · next q' hq' =>
        exact Or.inl ⟨FrameCarrier.ofFrame (E := E) p, by
          simpa [accepted] using toList_push_ok (E := E) c.out (FrameCarrier.ofFrame (E := E) p) q' hq',
          rfl⟩
      · next => exact Or.inr ⟨rfl, rfl⟩
    · next => exact Or.inr ⟨rfl, rfl⟩

/-- The run a sender's wire carries is flag-free: `Transparent.body_flag_free` at the decomposition.
A supporting lemma. `[PROVED: kernel]` -/
theorem encRun_flag_free (flag : Nat) [StuffedChannel.Transparent C flag] (p : Frame)
    (run : List Nat) (hrun : EncRun (C := C) (K := K) flag p run) : ∀ b ∈ run, b ≠ flag := by
  obtain ⟨heq, _⟩ := hrun
  intro b hb
  have hdl : (StuffedChannel.encodeStuffed (C := C) (K := K) p).dropLast = run := by
    rw [heq]; simp
  exact StuffedChannel.wire_flag_free_of_send (C := C) (K := K) flag p b (by rw [hdl]; exact hb)

/-- A well-formed frame's encoding is accepted, in order, with nothing dropped, and the receiver is
left at a run boundary. The `room` hypothesis is the price of counting a full-queue refusal as a
drop; the `EncRun` hypothesis is why this does not contradict `idle_flags` -- see the module
docstring. `[PROVED: kernel]` -/
theorem feed_frame (c : Rcv Q) (flag : Nat) [StuffedChannel.Transparent C flag] (p : Frame)
    (run : List Nat) (hp : FrameOK p) (hrun : EncRun (C := C) (K := K) flag p run)
    (hroom : QueueModel.full (Q := Q) (α := E) c.out = false) (hbuf : c.buf = []) :
    accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c
          (StuffedChannel.encodeStuffed (C := C) (K := K) p))
        = accepted (Q := Q) (E := E) c ++ [FrameCarrier.ofFrame (E := E) p] ∧
      (feed (C := C) (K := K) (E := E) flag c
          (StuffedChannel.encodeStuffed (C := C) (K := K) p)).dropped = c.dropped ∧
      (feed (C := C) (K := K) (E := E) flag c
          (StuffedChannel.encodeStuffed (C := C) (K := K) p)).buf = [] := by
  rung manual =>
    obtain ⟨heq, hne⟩ := hrun
    have hfree : ∀ b ∈ run, b ≠ flag :=
      encRun_flag_free (C := C) (K := K) flag p run ⟨heq, hne⟩
    have hparse : acceptRun (C := C) (K := K) flag run = .ok (p, []) := by
      unfold acceptRun
      rw [← heq]
      simpa using StuffedChannel.parseStuffed_encodeStuffed (C := C) (K := K) flag p [] hp
    have hnf : ¬ QueueModel.full (Q := Q) (α := E) c.out := by simp [hroom]
    obtain ⟨q', hq', htl⟩ :=
      BoundedQueueLaws.push_law c.out (FrameCarrier.ofFrame (E := E) p) hnf
    rw [heq, feed_run_eq (C := C) (K := K) (E := E) flag c run hfree hbuf]
    have hb : ({ c with buf := run } : Rcv Q).buf.isEmpty = false := by simpa using hne
    unfold finishRun
    rw [if_neg (by simp [hb])]
    simp only []
    rw [hparse]
    simp only []
    rw [hq']
    exact ⟨by simpa [accepted] using htl, rfl, rfl⟩

/-- Every accepted frame comes from a flag-delimited run actually present in the bytes fed, with
`accepted` and the run witness related through the acceptance test. The general form, over a receiver
that may already be mid-run. A supporting lemma. `[PROVED: kernel]` -/
theorem feed_sound (flag : Nat) (c : Rcv Q) (w : List Nat) (hinv : ∀ b ∈ c.buf, b ≠ flag) :
    ∀ x ∈ accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c w),
      x ∈ accepted (Q := Q) (E := E) c ∨
      ∃ (pre run suf : List Nat) (p : Frame) (rest : List Nat),
        c.buf ++ w = pre ++ (run ++ [flag]) ++ suf ∧ (∀ b ∈ run, b ≠ flag) ∧ run ≠ [] ∧
          acceptRun (C := C) (K := K) flag run = .ok (p, rest) ∧
          x = FrameCarrier.ofFrame (E := E) p := by
  induction w generalizing c with
  | nil => intro x hx; exact Or.inl (by simpa [feed_nil] using hx)
  | cons b t ih =>
    intro x hx
    rw [feed_cons] at hx
    by_cases hb : b = flag
    · have hstep : step (C := C) (K := K) (E := E) flag c b
          = finishRun (C := C) (K := K) (E := E) flag c := by
        simp [step, hb]
      rw [hstep] at hx
      have hinv' : ∀ y ∈ (finishRun (C := C) (K := K) (E := E) flag c).buf, y ≠ flag := by
        rw [finishRun_buf (C := C) (K := K) (E := E) flag c]; simp
      rcases ih (finishRun (C := C) (K := K) (E := E) flag c) hinv' x hx with hacc | hwit
      · -- the frame was already accepted before this flag, or was accepted BY this flag
        by_cases he : c.buf.isEmpty
        · left
          have : finishRun (C := C) (K := K) (E := E) flag c = c := by simp [finishRun, he]
          rwa [this] at hacc
        · -- a non-empty run: the flag judged it
          have hrun : c.buf ≠ [] := by simpa using he
          unfold finishRun at hacc
          rw [if_neg (by simp [he])] at hacc
          split at hacc
          · next p rest hpr =>
            split at hacc
            · next q' hq' =>
              have htl := toList_push_ok (E := E) c.out (FrameCarrier.ofFrame (E := E) p) q' hq'
              rw [show (accepted (Q := Q) (E := E) { out := q', buf := ([] : List Nat), dropped := c.dropped })
                    = QueueModel.toList (Q := Q) (α := E) q' from rfl, htl] at hacc
              rcases List.mem_append.mp hacc with h1 | h2
              · exact Or.inl h1
              · refine Or.inr ⟨[], c.buf, t, p, rest, ?_, hinv, hrun, hpr, ?_⟩
                · rw [hb]; simp
                · simpa using h2
            · next => exact Or.inl hacc
          · next => exact Or.inl hacc
      · obtain ⟨pre, run, suf, p, rest, heq, hfree, hne, hpr, hxp⟩ := hwit
        rw [finishRun_buf (C := C) (K := K) (E := E) flag c] at heq
        refine Or.inr ⟨c.buf ++ [b] ++ pre, run, suf, p, rest, ?_, hfree, hne, hpr, hxp⟩
        simp only [List.nil_append] at heq
        rw [show c.buf ++ (b :: t) = c.buf ++ [b] ++ t by simp, heq]
        simp
    · have hstep : step (C := C) (K := K) (E := E) flag c b = { c with buf := c.buf ++ [b] } := by
        simp [step, hb]
      rw [hstep] at hx
      have hinv' : ∀ y ∈ ({ c with buf := c.buf ++ [b] } : Rcv Q).buf, y ≠ flag := by
        intro y hy
        rcases List.mem_append.mp hy with h1 | h2
        · exact hinv y h1
        · have hy : y = b := by simpa using h2
          rw [hy]; exact hb
      rcases ih { c with buf := c.buf ++ [b] } hinv' x hx with hacc | hwit
      · exact Or.inl hacc
      · obtain ⟨pre, run, suf, p, rest, heq, hfree, hne, hpr, hxp⟩ := hwit
        refine Or.inr ⟨pre, run, suf, p, rest, ?_, hfree, hne, hpr, hxp⟩
        rw [show c.buf ++ (b :: t) = c.buf ++ [b] ++ t by simp]
        simpa using heq

/-- SOUNDNESS: every frame a fresh receiver accepts off an arbitrary byte stream is the acceptance
test's own reading of a non-empty, flag-free, flag-terminated run that occurs in that stream. No
frame is invented out of corruption.

The witnessing run is explicit rather than the accepted frame's own encoding, and that is not
defensiveness: the encoding form is refuted in the kernel at `[129, 0, 0, 0, 126]` (see the module
docstring). `[PROVED: kernel]` -/
theorem accepted_sound (c : Rcv Q) (flag : Nat) (w : List Nat) (hbuf : c.buf = [])
    (hempty : accepted (Q := Q) (E := E) c = []) :
    ∀ x ∈ accepted (Q := Q) (E := E) (feed (C := C) (K := K) (E := E) flag c w),
      ∃ (pre run suf : List Nat) (p : Frame) (rest : List Nat),
        w = pre ++ (run ++ [flag]) ++ suf ∧ (∀ b ∈ run, b ≠ flag) ∧ run ≠ [] ∧
          acceptRun (C := C) (K := K) flag run = .ok (p, rest) ∧
          x = FrameCarrier.ofFrame (E := E) p := by
  rung manual =>
    intro x hx
    rcases feed_sound (C := C) (K := K) (E := E) flag c w (by simp [hbuf]) x hx with hacc | hwit
    · rw [hempty] at hacc; exact absurd hacc (by simp)
    · obtain ⟨pre, run, suf, p, rest, heq, hfree, hne, hpr, hxp⟩ := hwit
      rw [hbuf] at heq
      exact ⟨pre, run, suf, p, rest, by simpa using heq, hfree, hne, hpr, hxp⟩

end runs

#print axioms poll_accepted
#print axioms feed_append
#print axioms quiet_before_flag
#print axioms idle_flags
#print axioms run_exactly_one
#print axioms feed_frame
#print axioms accepted_sound

end FramedChannel.Receiver
