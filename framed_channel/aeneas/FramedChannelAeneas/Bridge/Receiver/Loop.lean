-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Receiver.Defs
import FramedChannelAeneas.Bridge.StuffedChannel.Frame
import FramedChannel.Composition.Receiver.Theorems

/-!
# Bridge/Receiver/Loop: the extracted `feed` loop refines the model's fold

`[EXTRACTED: aeneas + bridge]` -- the scan side of the receive-path bridge. `feed_loop_refines`
proves that the Charon/Aeneas extraction of `rust/src/receiver.rs`'s `feed` loop agrees with
`FramedChannel.Receiver.feed` on every input slice, and `finish_run_refines` proves the same for the
run judgement the loop calls at every flag.

## The unconditional-stride loop

`Bridge/Stuff/Unstuff.lean`'s loop advances by one or two indices and has **seven** exits. This one
advances by one, unconditionally, and has **three**: the index has reached the end of the wire, the
`get` returned `none`, and a byte was read (which then splits into the flag and the ordinary cases).
That is the whole termination argument, structural rather than argued: the measure
`bytes.len() - i` strictly decreases on every branch, the rejected run included, because `i += 1`
sits outside every conditional in the Rust.

## The invariant

`FeedInv` says four things. The index is within the wire; the buffered run plus the wire still to
come fits a `usize`; the drop count plus the wire still to come fits a `usize`; and -- the content --
the extracted receiver is related to the model's fold over exactly the bytes consumed so far.

The two `usize` conjuncts are what discharge the extraction's two panic sites without a hypothesis
at every branch: at `i < len` the remaining wire is at least one byte, so each bound gives strict
inequality, and each is preserved because a `push` moves one byte from the second summand to the
first while `finish_run` empties the buffer and adds at most one drop (`finishRun_dropped_le`).

## The wide-length side condition

`finish_run` hands the buffered run to `stuffed_channel::parse_stuffed`, so it inherits
`ParsePost`'s `DeclaresWideLength` disjunct: the model's unbounded varint accepts a declared length
of `2 ^ 32` or more where the extracted `decode_u32` rejects it. `finish_run_refines` states that
disjunct honestly. The loop cannot, because it judges many runs, so it takes `NoWideRun` as a
hypothesis: no run *this receiver will judge* declares such a length. That is stated entirely in
model terms -- over `(feed … (take k)).buf` for each prefix -- so a client discharges it by knowing
what it fed, and `certificate/receiver.yaml` records it under `assumptions:`.

## The two hypotheses on the drop counter and the buffer

`finish_run`'s `dropped.saturating_add(1)` makes the extracted call **total**: there is no panic and
no overflow obligation, which is what Decision 5 bought. It does not make the two counters *agree*:
`saturating_add` caps at `Usize.max` while the model's `Nat` does not, so relating the values needs
`dropped < usize::MAX`. That is a real extracted behaviour, stated rather than hidden, exactly as
`send_refines`'s `hovf` and `hw` are. The buffer bound is the panic obligation of `Vec::push`, the
analogue of `Bridge/Stuff/Stuff.lean`'s `out.length + 2 * payload.length <= usize::MAX`.

## Scope

`finish_run_refines` is here rather than in `Refinement.lean` beside the other operations, because
the loop calls it: it is the loop's own step lemma. `finish_run` is private in Rust and is covered by
its bridge row, not by a differential vector. `finishRun_dropped_le` is proved here rather than in
the core model, as `Bridge/Stuff/Unstuff.lean`'s equation lemmas are, so that the approved
`Composition/Receiver/Theorems.lean` did not have to change. None of the declarations in this module
is registered (Decision 11).
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.receiver
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf bytesOf_append bytesOf_length marker_eq)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Bridge.channel (ofFrame_bitsOf)
open FramedChannel.Bridge.stuffed_channel (ParsePost DeclaresWideLength parse_stuffed_refines)
open FramedChannel.Channel (Frame FrameCarrier)
open FramedChannel.Receiver (Rcv finishRun acceptRun)

section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
include hsim

theorem finish_run_refines (c : receiver.Receiver S)
    (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : RcvRel c m)
    (hbuf : c.buf.val.length < Usize.max) (hdropmax : c.dropped.val < Usize.max) :
    receiver.Receiver.finish_run inst c ⦃ c' =>
      DeclaresWideLength (m.buf ++ [FramedChannel.Stuff.marker]) ∨
        RcvRel c' (finishRun (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker m) ⦄ := by
  obtain ⟨hout, hbufeq, hdrop⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hout ▸ hq
  unfold receiver.Receiver.finish_run
  step*
  case h1 =>
    -- the idle branch: an empty run is ignored, never counted (RFC 1662 4.1)
    have hb : b = true := ‹b = true›
    have hce : c.buf.val = [] := by rw [hb] at b_post; simpa using b_post.symm
    have hmb : m.buf = [] := by rw [← hbufeq, hce]; simp [bytesOf]
    refine Or.inr ?_
    have hfr : finishRun (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
        (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker m = m := by
      simp [FramedChannel.Receiver.finishRun, hmb]
    rw [hfr]
    exact ⟨hout, hbufeq, hdrop⟩
  -- the non-empty run: terminated with one flag and handed whole to the run parser
  have hbne : ¬ b = true := ‹¬ b = true›
  have hne : c.buf.val ≠ [] := by
    intro hc; rw [hc] at b_post; simp at b_post; exact hbne b_post
  have hmne : ¬ m.buf.isEmpty = true := by rw [← hbufeq]; simpa [bytesOf] using hne
  have hderef : (alloc.vec.Vec.deref v).val = v.val := by
    simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  have hvb : bytesOf v.val = m.buf ++ [FramedChannel.Stuff.marker] := by
    rw [v_post, bytesOf_append, hbufeq]; simp [bytesOf, marker_eq]
  step with parse_stuffed_refines as ⟨o, hpost⟩
  rw [hderef, hvb] at hpost
  rcases o with _ | ⟨payload, used⟩
  · -- the run parser refused: one drop, or the varint layer's divergence
    step with FramedChannel.Bridge.usize_saturating_add_spec as ⟨i1, hi1⟩
    rcases hpost with hfail | hwide
    · refine Or.inr ?_
      have hfr : finishRun (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker m
          = { out := m.out, buf := [], dropped := m.dropped + 1 } := by
        simp only [FramedChannel.Receiver.finishRun, if_neg hmne,
          FramedChannel.Receiver.acceptRun, hfail]
      rw [hfr]
      have hle : c.dropped.val + 1 ≤ Usize.max := by omega
      exact ⟨hout, by simp [bytesOf], by rw [hi1, min_eq_right hle, ← hdrop]⟩
    · exact Or.inl hwide
  · -- the run parser took the run: one accepted frame, or one drop if the queue refuses
    obtain ⟨hused, hparse⟩ := hpost
    step*
    by_cases hfull : QueueModel.full (Q := Q) (α := alloc.vec.Vec Std.U8) q
    · obtain ⟨p, hp, hpe⟩ := (WP.spec_equiv_exists _ _).mp
        (hsim.push_full c.out q payload hq' hfull)
      have hext : QueueModel.push (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R) m.out payload
          = .fail := by
        show extPush m.out payload = _
        simp only [extPush, ← hout, hp, Result.match.ok, hpe]
      have hfr : finishRun (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker m
          = { out := m.out, buf := [], dropped := m.dropped + 1 } := by
        simp only [FramedChannel.Receiver.finishRun, if_neg hmne,
          FramedChannel.Receiver.acceptRun, hparse, ofFrame_bitsOf, hext]
      rw [hp, hpe]
      step*
      refine Or.inr ?_
      rw [hfr]
      have hle : c.dropped.val + 1 ≤ Usize.max := by omega
      have hone : (1#usize : Usize).val = 1 := rfl
      exact ⟨hout, by simp [bytesOf],
        by rw [FramedChannel.Bridge.usize_saturating_add_val, hone, min_eq_right hle, ← hdrop]⟩
    · obtain ⟨p, hp, hok, q', hpush, hR'⟩ := (WP.spec_equiv_exists _ _).mp
        (hsim.push_ok c.out q payload hq' hfull)
      obtain ⟨e, t⟩ := p
      simp only at hok hR'
      subst hok
      have hext : QueueModel.push (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R) m.out payload
          = .ok ⟨t, q', hR'⟩ := by
        show extPush m.out payload = _
        simp only [extPush, ← hout, hp, Result.match.ok]
        rw [dif_pos ⟨q', hR'⟩]
      have hfr : finishRun (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker m
          = { out := ⟨t, q', hR'⟩, buf := [], dropped := m.dropped } := by
        simp only [FramedChannel.Receiver.finishRun, if_neg hmne,
          FramedChannel.Receiver.acceptRun, hparse, ofFrame_bitsOf, hext]
      rw [hp]
      step*
      refine Or.inr ?_
      rw [hfr]
      exact ⟨rfl, by simp [bytesOf], hdrop⟩

end

section loop
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}

local notation "MFEED" => FramedChannel.Receiver.feed (C := FramedChannel.Stuff.Hdlc)
  (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker

def FeedInv (bytes : Slice Std.U8) (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R))
    (x : receiver.Receiver S × Std.Usize) : Prop :=
  x.2.val ≤ bytes.val.length ∧
    x.1.buf.val.length + (bytes.val.length - x.2.val) ≤ Usize.max ∧
    x.1.dropped.val + (bytes.val.length - x.2.val) ≤ Usize.max ∧
    RcvRel x.1 (MFEED m ((bytesOf bytes.val).take x.2.val))

def FeedPost (bytes : Slice Std.U8) (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R))
    (c' : receiver.Receiver S) : Prop :=
  RcvRel c' (MFEED m (bytesOf bytes.val))

theorem bytesOf_take_succ (l : List Std.U8) (k : Nat) (hk : k < l.length) :
    (bytesOf l).take (k + 1) = (bytesOf l).take k ++ [(l[k]).val] := by
  have hk' : k < (bytesOf l).length := by rw [bytesOf_length]; exact hk
  rw [List.take_add_one, List.getElem?_eq_getElem hk']
  simp [bytesOf]

/-- The model's drop counter grows by at most one per run. Proved here rather than in the core model,
as `Bridge/Stuff/Unstuff.lean`'s equation lemmas are, so the approved core module did not have to
change. -/
theorem finishRun_dropped_le (flag : Nat)
    (r : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R)) :
    (FramedChannel.Receiver.finishRun (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) flag r).dropped
      ≤ r.dropped + 1 := by
  unfold FramedChannel.Receiver.finishRun
  split
  · omega
  · split
    · split <;> simp
    · simp

/-- The loop lemma: the extracted `feed_loop` refines the model's fold, on a measure that decreases
on every branch. -/
theorem feed_loop_refines (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
    (bytes : Slice Std.U8) (m : Rcv (Ext S Q (alloc.vec.Vec Std.U8) inst R))
    (hnw : NoWideRun bytes m) (x : receiver.Receiver S × Std.Usize) (hx : FeedInv bytes m x) :
    receiver.Receiver.feed_loop inst x.1 bytes x.2 ⦃ c' => FeedPost bytes m c' ⦄ := by
  unfold receiver.Receiver.feed_loop
  apply loop.spec_decr_nat
    (measure := fun (y : receiver.Receiver S × Std.Usize) => bytes.val.length - y.2.val)
    (inv := FeedInv bytes m)
  · rintro ⟨c, i⟩ ⟨hile, hbufb, hdropb, hRel⟩
    simp only at hile hbufb hdropb hRel
    unfold receiver.Receiver.feed_loop.body
    step*
    · -- `get` at `i` returned `none`: the wire has run out
      have hnone : o = none := ‹o = none›
      rw [hnone] at o_post
      have hge : bytes.val.length ≤ i.val := List.getElem?_eq_none_iff.mp o_post.symm
      simp only [FeedPost]
      rwa [List.take_of_length_le (by rw [bytesOf_length]; omega)] at hRel
    · -- a byte off the wire: the flag ends the run, anything else extends it
      have hsome : o = some b := ‹o = some b›
      have hlt : i.val < bytes.val.length := by
        have h1 : i.val < (Slice.len bytes).val := by simpa using ‹i < bytes.len›
        simpa using h1
      have hget : bytes.val[i.val]? = some b := by rw [← o_post, hsome]
      have hb : b = bytes.val[i.val] := by
        rw [List.getElem?_eq_getElem hlt] at hget; exact (Option.some.inj hget).symm
      have htake : (bytesOf bytes.val).take (i.val + 1)
          = (bytesOf bytes.val).take i.val ++ [b.val] := by
        rw [bytesOf_take_succ bytes.val i.val hlt, ← hb]
      have hstep : MFEED m ((bytesOf bytes.val).take (i.val + 1))
          = FramedChannel.Receiver.step (C := FramedChannel.Stuff.Hdlc)
              (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8)
              FramedChannel.Stuff.marker (MFEED m ((bytesOf bytes.val).take i.val)) b.val := by
        rw [htake, FramedChannel.Receiver.feed_append, FramedChannel.Receiver.feed_cons,
          FramedChannel.Receiver.feed_nil]
      by_cases hbm : b = stuff.MARKER
      · -- the flag: judge the buffered run
        have hbv : b.val = FramedChannel.Stuff.marker := by rw [hbm, marker_eq]
        have hbuflt : c.buf.val.length < Usize.max := by omega
        have hdroplt : c.dropped.val < Usize.max := by omega
        rw [if_pos hbm]
        step with finish_run_refines hsim c _ hRel hbuflt hdroplt as ⟨c1, hc1⟩
        have hc1' : RcvRel c1 (FramedChannel.Receiver.finishRun
            (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
            (E := alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker
            (MFEED m ((bytesOf bytes.val).take i.val))) := by
          rcases hc1 with hwide | hok
          · exact absurd hwide (hnw i.val (by omega))
          · exact hok
        step*
        refine ⟨?_, ?_⟩
        · refine ⟨by rw [i2_post]; omega, ?_, ?_, ?_⟩
          · obtain ⟨_, hb1, _⟩ := hc1'
            have hnil : c1.buf.val = [] := by
              have := hb1
              rw [FramedChannel.Receiver.finishRun_buf (C := FramedChannel.Stuff.Hdlc)
                (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8)] at this
              simpa [bytesOf] using this
            rw [i2_post, hnil]; simp; omega
          · obtain ⟨_, _, hd1⟩ := hc1'
            rw [i2_post, hd1]
            have hdr : (FramedChannel.Receiver.finishRun (C := FramedChannel.Stuff.Hdlc)
                (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8)
                FramedChannel.Stuff.marker
                (MFEED m ((bytesOf bytes.val).take i.val))).dropped
                ≤ (MFEED m ((bytesOf bytes.val).take i.val)).dropped + 1 :=
              finishRun_dropped_le _ _
            obtain ⟨_, _, hd0⟩ := hRel
            omega
          · rw [i2_post, hstep]
            simpa [FramedChannel.Receiver.step, hbv] using hc1'
        · rw [i2_post]; omega
      · -- an ordinary byte: it extends the run
        have hbv : b.val ≠ FramedChannel.Stuff.marker := by
          intro hv; exact hbm (Std.UScalar.eq_of_val_eq (by rw [hv, marker_eq]))
        have hbuflt : c.buf.val.length < Usize.max := by omega
        rw [if_neg hbm]
        step*
        refine ⟨?_, ?_⟩
        · obtain ⟨hout1, hbuf1, hdrop1⟩ := hRel
          have hi2 : i2.val ≤ bytes.val.length := by rw [i2_post]; omega
          refine ⟨hi2, ?_, ?_, ?_⟩
          · show x.val.length + (bytes.val.length - i2.val) ≤ Usize.max
            rw [i2_post, x_post]; simp; omega
          · show c.dropped.val + (bytes.val.length - i2.val) ≤ Usize.max
            rw [i2_post]; omega
          · show RcvRel { out := c.out, buf := x, dropped := c.dropped }
              (MFEED m ((bytesOf bytes.val).take i2.val))
            rw [i2_post, hstep]
            simp only [RcvRel, FramedChannel.Receiver.step, if_neg hbv]
            refine ⟨hout1, ?_, hdrop1⟩
            rw [x_post, bytesOf_append, hbuf1]
            simp [bytesOf]
        · rw [i2_post]; omega
    · -- the index has reached the end of the wire
      have hge : bytes.val.length ≤ i.val := by
        have h1 : ¬ i.val < (Slice.len bytes).val := by simpa using ‹¬ i < bytes.len›
        simpa using h1
      simp only [FeedPost]
      rwa [List.take_of_length_le (by rw [bytesOf_length]; omega)] at hRel
  · exact hx

end loop
end FramedChannel.Bridge.receiver

#print axioms FramedChannel.Bridge.receiver.finish_run_refines
#print axioms FramedChannel.Bridge.receiver.feed_loop_refines
