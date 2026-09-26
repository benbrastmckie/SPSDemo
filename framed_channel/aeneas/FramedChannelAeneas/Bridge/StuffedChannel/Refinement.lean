-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.StuffedChannel.Frame

/-!
# Bridge/StuffedChannel/Refinement: the extracted operations, once over any queue record

`[EXTRACTED: aeneas + bridge]` -- per-operation simulation of `rust/src/stuffed_channel.rs`'s
`send`, `deliver`, `take` and `queued`, as extracted, against the specification channel
`StuffedChannel.send`/`deliver` at `SChan (Ext S Q (Vec U8) inst R)`.

## Stated once, over any lawful record

Charon and Aeneas turn the channel's `Q: BoundedQueue<Frame>` bound into an explicit record argument
`inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)`. Every theorem here quantifies over that
record, a model queue `Q`, and a simulation `hsim : QueueSim S Q (Vec U8) inst R` with a functional
relation `R` (`hfun`). None names the ring buffer or the list-backed queue: the queue is reached only
through `hsim`'s fields and `Bridge/Queue/Instance.lean`'s `extToList_eq` and `extCapacity_eq`. The
frame codec is reached only through `Frame.lean` beside this file. `Instance.lean` then instantiates
each consequence at both extracted queues.

## The divergence carried by `deliver`

`deliver_refines` inherits `ParsePost`'s case split: when the frame at the head of the wire declares
a length of `2 ^ 32` or more, the extraction refuses it where the model would try to read it. That is
the varint layer's divergence and the only one, and no wire the channel wrote contains such a frame.

## The wire-room hypothesis

`send_refines` needs `c.wire.length + 2 * payload.length + 13 ≤ Usize.max`, where `Channel`'s needed
`+ 7`: stuffing can double the body, and the body is the payload plus at most six bytes. Both are the
same kind of hypothesis -- Aeneas bounds a `Vec` by `Usize.max` and panics beyond it -- and this one
is simply the transparent format's own worst case.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Bridge.channel (ofFrame_bitsOf)
open FramedChannel.Channel (Frame FrameCarrier FrameOK)
open FramedChannel.StuffedChannel (SChan encodeStuffed parseStuffed)

section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hsim hfun

/-- Send refinement, over any lawful extracted queue record: the extracted `send` succeeds exactly
when the specification's `send` does, and then the two channels are related again; it refuses
(`Err`, state unchanged) exactly when the specification fails.

Two hypotheses remain, and both are genuine extracted behavior rather than proof artifacts:
* `hovf`: queued plus in-flight fits a `usize`. The Rust adds `len()` and `in_flight` before the
  capacity compare, and Aeneas models that add's overflow as a panic. Every composite theorem
  discharges it from `SChanInv`, whose fourth conjunct bounds the sum by the capacity, itself a
  `usize`.
* `hw`: room on the wire for the stuffed frame. It excludes only payloads within a small constant
  factor of that bound. `[EXTRACTED: aeneas + bridge]` -/
theorem send_refines (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (payload : Slice Std.U8)
    (hR : SChanRel c m)
    (hovf : (QueueModel.toList (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
      (α := alloc.vec.Vec Std.U8) m.out).length + m.inFlight ≤ Usize.max)
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c' =>
      (∀ m', FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val)
            = .ok m' → r = .Ok () ∧ SChanRel c' m') ∧
      (FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val)
            = .fail → r = .Err () ∧ c' = c) ⦄ := by
  obtain ⟨hout, hwire, hfl⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hout ▸ hq
  have hlist := extToList_eq (T := alloc.vec.Vec Std.U8) hfun m.out q hq
  have hcap := extCapacity_eq hsim m.out q hq
  unfold stuffed_channel.StuffedChannel.send
  step with hsim.len c.out q hq' as ⟨n, hn⟩
  have hadd : n.val + c.in_flight.val ≤ Usize.max := by rw [hn, hfl, ← hlist]; exact hovf
  step*
  step with hsim.capacity c.out q hq' as ⟨k, hk⟩
  by_cases hge : (QueueModel.toList (Q := Q) (α := alloc.vec.Vec Std.U8) q).length + m.inFlight
      ≥ QueueModel.capacity (Q := Q) (α := alloc.vec.Vec Std.U8) q
  · have hmf : FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val)
          = .fail := by
      unfold FramedChannel.StuffedChannel.send; rw [if_pos (by rw [hlist, hcap]; exact hge)]
    have hge' : i1 ≥ k := by scalar_tac
    step*
  · have hlt' : ¬ i1 ≥ k := by scalar_tac
    have hkmax : k.val ≤ Usize.max := by scalar_tac
    by_cases hlong : 2 ^ 32 ≤ (bitsOf payload.val).length
    · have hmf : FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val)
            = .fail := by
        unfold FramedChannel.StuffedChannel.send
        rw [if_neg (by rw [hlist, hcap]; exact hge), if_pos hlong]
      have hl : U32.max < payload.len.val := by simp [bitsOf] at hlong; scalar_tac
      step*
    · have hl : payload.len.val ≤ U32.max := by simp [bitsOf] at hlong; scalar_tac
      step*
      rename_i hr
      obtain ⟨x, hx, hxv⟩ := r_post hl
      rw [hr] at hx
      cases hx
      have hlen : len.val = payload.val.length := by rw [hxv]; simp
      step with encode_stuffed_refines payload len c.wire hlen hw as ⟨v, hv⟩
      step*
      have hmo : FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val)
            = .ok ⟨m.out, m.wire ++ encodeStuffed (C := FramedChannel.Stuff.Hdlc)
                (K := FramedChannel.Crc8.Bitwise) (bitsOf payload.val), m.inFlight + 1⟩ := by
        unfold FramedChannel.StuffedChannel.send
        rw [if_neg (by rw [hlist, hcap]; exact hge), if_neg hlong]
      refine ⟨?_, ?_⟩
      · intro m' hm'
        rw [hmo] at hm'
        cases hm'
        simp only [SChanRel]
        exact ⟨hout, by rw [hv, hwire], by simp only [i4_post, hfl]⟩
      · intro hf
        rw [hmo] at hf
        cases hf

omit hfun in
/-- Take refinement: the extracted `take` pops exactly what the specification's queue pops, and
returns `None` with the channel unchanged exactly when the specification's pop fails.
`[EXTRACTED: aeneas + bridge]` -/
theorem take_refines (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : SChanRel c m) :
    stuffed_channel.StuffedChannel.take inst c ⦃ o c' =>
      match QueueModel.pop (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
          (α := alloc.vec.Vec Std.U8) m.out with
      | .ok (y, q') => o = some y ∧ SChanRel c' { m with out := q' }
      | .fail => o = none ∧ c' = c ⦄ := by
  obtain ⟨hout, hwire, hfl⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hout ▸ hq
  unfold stuffed_channel.StuffedChannel.take
  by_cases he : QueueModel.empty (Q := Q) (α := alloc.vec.Vec Std.U8) q
  · obtain ⟨p, hp, hpe⟩ := (WP.spec_equiv_exists _ _).mp (hsim.pop_empty c.out q hq' he)
    have hext : QueueModel.pop (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
        (α := alloc.vec.Vec Std.U8) m.out = .fail := by
      show extPop m.out = _
      simp only [extPop, ← hout, hp, Result.match.ok, hpe]
    rw [hp, hpe]
    simp only [bind_tc_ok]
    rw [hext]
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
    rw [hext]
    exact ⟨rfl, rfl, hwire, hfl⟩

/-- `queued` is the length of the specification queue's contents. `[EXTRACTED: aeneas + bridge]` -/
theorem queued_agrees (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : SChanRel c m) :
    stuffed_channel.StuffedChannel.queued inst c ⦃ n =>
      n.val = (QueueModel.toList (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R)
        (α := alloc.vec.Vec Std.U8) m.out).length ⦄ := by
  obtain ⟨hout, -, -⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  unfold stuffed_channel.StuffedChannel.queued
  rw [extToList_eq (T := alloc.vec.Vec Std.U8) hfun m.out q hq]
  exact hsim.len c.out q (hout ▸ hq)

omit hfun in
/-- Deliver refinement, over any lawful extracted queue record. When the specification's `deliver`
succeeds, the extracted `deliver` returns `Ok v` where `v` reads as exactly the frame the
specification parsed, and the channels are related again, **or** the wire's head frame declares a
length of `2 ^ 32` or more (`DeclaresWideLength`, the varint layer's divergence). When the
specification's `deliver` fails, the extracted one returns `Err` with the channel unchanged. No
hypothesis: the pushed element is `v` itself (`cloneVecU8_isId`), which is the carrier of the parsed
frame (`ofFrame_bitsOf`). `[EXTRACTED: aeneas + bridge]` -/
theorem deliver_refines (c : stuffed_channel.StuffedChannel S)
    (m : SChan (Ext S Q (alloc.vec.Vec Std.U8) inst R)) (hR : SChanRel c m) :
    stuffed_channel.StuffedChannel.deliver inst c ⦃ r c' =>
      (∀ m', FramedChannel.StuffedChannel.deliver (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m = .ok m' →
        (∃ v p rest, r = .Ok v ∧ parseStuffed (C := FramedChannel.Stuff.Hdlc)
            (K := FramedChannel.Crc8.Bitwise) m.wire = .ok (p, rest) ∧ bitsOf v.val = p ∧
            SChanRel c' m') ∨
        DeclaresWideLength m.wire) ∧
      (FramedChannel.StuffedChannel.deliver (C := FramedChannel.Stuff.Hdlc)
          (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m = .fail →
        r = .Err () ∧ c' = c) ⦄ := by
  obtain ⟨hout, hwire, hfl⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hout ▸ hq
  have hderef : (alloc.vec.Vec.deref c.wire).val = c.wire.val := by
    simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  unfold stuffed_channel.StuffedChannel.deliver
  step with parse_stuffed_refines as ⟨o, hpost⟩
  rw [hderef, hwire] at hpost
  have hdeliver : ∀ p rest, parseStuffed (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) m.wire = .ok (p, rest) →
      FramedChannel.StuffedChannel.deliver (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m =
        (match QueueModel.push m.out (FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) p) with
         | .ok q' => .ok { out := q', wire := rest, inFlight := m.inFlight - 1 }
         | .fail => .fail) := by
    intro p rest h
    unfold FramedChannel.StuffedChannel.deliver
    simp only [h]
    split <;> rename_i heq <;> simp only [heq]
  rcases o with _ | ⟨payload, used⟩
  · simp only [ParsePost] at hpost
    simp only [WP.spec_ok]
    refine ⟨?_, fun _ => ⟨rfl, rfl⟩⟩
    intro m' hm'
    rcases hpost with hf | hwide
    · unfold FramedChannel.StuffedChannel.deliver at hm'
      rw [hf] at hm'
      cases hm'
    · exact Or.inr hwide
  · simp only [ParsePost] at hpost
    obtain ⟨hused, hparse⟩ := hpost
    have hcl : alloc.vec.CloneVec.clone core.clone.CloneU8 payload = ok payload :=
      cloneVecU8_isId payload
    step*
    rw [hcl]
    simp only [bind_tc_ok]
    have hmp := hdeliver _ _ hparse
    rw [ofFrame_bitsOf] at hmp
    by_cases hfull : QueueModel.full (Q := Q) (α := alloc.vec.Vec Std.U8) q
    · obtain ⟨p, hp, hpe⟩ := (WP.spec_equiv_exists _ _).mp
        (hsim.push_full c.out q payload hq' hfull)
      have hext : QueueModel.push (Q := Ext S Q (alloc.vec.Vec Std.U8) inst R) m.out payload
          = .fail := by
        show extPush m.out payload = _
        simp only [extPush, ← hout, hp, Result.match.ok, hpe]
      rw [hext] at hmp
      rw [hp, hpe]
      simp only [bind_tc_ok]
      refine ⟨?_, fun _ => ⟨rfl, rfl⟩⟩
      intro m' hm'
      rw [hmp] at hm'
      cases hm'
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
      rw [hext] at hmp
      rw [hp]
      simp only [bind_tc_ok]
      step with drop_front_refines as ⟨v1, hv1⟩
      step*
      rw [hderef] at hv1
      refine ⟨?_, ?_⟩
      · intro m' hm'
        rw [hmp] at hm'
        cases hm'
        refine Or.inl ⟨payload, _, _, rfl, hparse, rfl, rfl, ?_, ?_⟩
        · rw [hv1, hwire]
        · simp only [i_post, hfl]
      · intro hf
        rw [hmp] at hf
        cases hf

end

end FramedChannel.Bridge.stuffed_channel

#print axioms FramedChannel.Bridge.stuffed_channel.send_refines
#print axioms FramedChannel.Bridge.stuffed_channel.take_refines
#print axioms FramedChannel.Bridge.stuffed_channel.queued_agrees
#print axioms FramedChannel.Bridge.stuffed_channel.deliver_refines
