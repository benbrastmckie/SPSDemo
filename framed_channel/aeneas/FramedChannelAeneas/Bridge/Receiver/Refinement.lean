-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Receiver.Loop

/-!
# Bridge/Receiver/Refinement: the extracted operations, once over any queue record

`[EXTRACTED: aeneas + bridge]` -- per-operation simulation of `rust/src/receiver.rs`'s `feed`,
`poll`, `dropped` and `queued`, as extracted, against the specification receiver
`Receiver.feed`/`poll` at `Rcv (Ext S Q (Vec U8) inst R)`. The private `finish_run` is in
`Loop.lean` beside the loop that calls it, and `with_queue`/`new` are in `Instance.lean`, following
`Bridge/Channel/`'s split.

## Stated once, over any lawful record

Charon and Aeneas turn the receiver's `Q: BoundedQueue<Frame>` bound into an explicit record
argument `inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)`. Every theorem here quantifies over
that record, a model queue `Q`, and a simulation `hsim : QueueSim S Q (Vec U8) inst R` with a
functional relation `R` (`hfun`). None names the ring buffer or the list-backed queue.

## `feed`'s three hypotheses

The plan expected one. There are three, and each is genuine extracted behavior rather than a proof
artifact:

* `hbufw`: the buffered run plus the fed bytes fit a `usize`. `Vec::push` panics beyond that bound,
  and the analogue of `Bridge/Stuff/Stuff.lean`'s `out.length + 2 * payload.length <= usize::MAX`.
* `hdropw`: the drop count plus the fed bytes fit a `usize`. This is the one Decision 5 expected to
  have bought away with `saturating_add`, and it bought half of it: the extracted call is **total**,
  so there is no panic obligation, but `saturating_add` caps at `Usize.max` where the model's `Nat`
  does not, so relating the two *values* needs the bound. Recorded rather than hidden.
* `hnw`: no run this receiver will judge declares a length of `2 ^ 32` or more. That is `ParsePost`'s
  `DeclaresWideLength` disjunct, inherited from the reused run parser and no more this unit's
  divergence than it was `StuffedChannel`'s. `Loop.lean`'s docstring explains why the loop takes it
  as a hypothesis where `finish_run_refines` can state it as a disjunct.

No wire the sender writes needs any of the three relaxed:
`Bridge/StuffedChannel/Frame.lean`'s `not_declaresWide_encodeStuffed` discharges `hnw` for such a
wire, and the other two are length bounds on real memory.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.receiver
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf bytesOf_length)
open FramedChannel.Channel (Frame FrameCarrier)
open FramedChannel.Receiver (Rcv)

section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hsim hfun

omit hfun in
/-- Feed refinement, over any lawful extracted queue record: the extracted `feed` leaves a receiver
related to the model's fold over the same bytes. Three hypotheses, all recorded in the module
docstring. `[EXTRACTED: aeneas + bridge]` -/
theorem feed_refines (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (bytes : Slice Std.U8)
    (hR : RcvRel c m) (hnw : NoWideRun bytes m)
    (hbufw : c.buf.val.length + bytes.val.length ≤ Usize.max)
    (hdropw : c.dropped.val + bytes.val.length ≤ Usize.max) :
    receiver.Receiver.feed inst c bytes ⦃ c' =>
      RcvRel c' (FramedChannel.Receiver.feed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8)
        FramedChannel.Stuff.marker m (bytesOf bytes.val)) ⦄ := by
  unfold receiver.Receiver.feed
  exact feed_loop_refines hsim bytes m hnw (c, 0#usize)
    ⟨by simp, by simpa using hbufw, by simpa using hdropw,
      by simpa [FramedChannel.Receiver.feed] using hR⟩

omit hfun in
/-- Poll refinement: the extracted `poll` hands back exactly what the specification's queue pops, and
returns `None` with the receiver unchanged exactly when the specification's pop fails.
`[EXTRACTED: aeneas + bridge]` -/
theorem poll_refines (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : RcvRel c m) :
    receiver.Receiver.poll inst c ⦃ o c' =>
      match FramedChannel.Receiver.poll (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
          (E := alloc.vec.Vec Std.U8) m with
      | .ok (y, m') => o = some y ∧ RcvRel c' m'
      | .fail => o = none ∧ c' = c ⦄ := by
  obtain ⟨hout, hbufeq, hdrop⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hout ▸ hq
  unfold receiver.Receiver.poll
  by_cases he : QueueModel.empty (Q := Q) (α := alloc.vec.Vec Std.U8) q
  · obtain ⟨p, hp, hpe⟩ := (WP.spec_equiv_exists _ _).mp (hsim.pop_empty c.out q hq' he)
    have hext : QueueModel.pop (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
        (α := alloc.vec.Vec Std.U8) m.out = .fail := by
      show extPop m.out = _
      simp only [extPop, ← hout, hp, Result.match.ok, hpe]
    rw [hp, hpe]
    simp only [bind_tc_ok]
    simp only [FramedChannel.Receiver.poll, hext]
    exact ⟨rfl, rfl⟩
  · obtain ⟨p, hp, y, q', hy, hpop, hR'⟩ := (WP.spec_equiv_exists _ _).mp
      (hsim.pop_ok c.out q hq' he)
    obtain ⟨o, s'⟩ := p
    simp only at hy hR'
    subst hy
    have hext : QueueModel.pop (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
        (α := alloc.vec.Vec Std.U8) m.out = .ok (y, ⟨s', q', hR'⟩) := by
      show extPop m.out = _
      simp only [extPop, ← hout, hp, Result.match.ok]
      rw [dif_pos ⟨q', hR'⟩]
    rw [hp]
    simp only [bind_tc_ok]
    simp only [FramedChannel.Receiver.poll, hext]
    exact ⟨rfl, rfl, hbufeq, hdrop⟩

omit hfun hsim in
/-- `dropped` is the specification's drop count. `[EXTRACTED: aeneas + bridge]` -/
theorem dropped_agrees (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : RcvRel c m) :
    receiver.Receiver.impl.dropped inst c ⦃ n => n.val = m.dropped ⦄ := by
  obtain ⟨-, -, hdrop⟩ := hR
  unfold receiver.Receiver.impl.dropped
  simpa using hdrop

/-- `queued` is the length of the specification queue's contents. `[EXTRACTED: aeneas + bridge]` -/
theorem queued_agrees (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : RcvRel c m) :
    receiver.Receiver.queued inst c ⦃ n =>
      n.val = (QueueModel.toList (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
        (α := alloc.vec.Vec Std.U8) m.out).length ⦄ := by
  obtain ⟨hout, -, -⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  unfold receiver.Receiver.queued
  rw [extToList_eq (T := alloc.vec.Vec Std.U8) hfun m.out q hq]
  exact hsim.len c.out q (hout ▸ hq)

end

end FramedChannel.Bridge.receiver

#print axioms FramedChannel.Bridge.receiver.feed_refines
#print axioms FramedChannel.Bridge.receiver.poll_refines
#print axioms FramedChannel.Bridge.receiver.dropped_agrees
#print axioms FramedChannel.Bridge.receiver.queued_agrees
