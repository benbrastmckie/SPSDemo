-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.StuffedChannel.Refinement

/-!
# Bridge/StuffedChannel/Composite: the composition theorems, at the extracted code

`[EXTRACTED: aeneas + bridge]` -- the composition theorems of
`lean/FramedChannel/Composition/StuffedChannel/Theorems.lean` (`send_deliver`, `deliver_spec`,
`send_inv`, `send_bounded`, `send_refuses_too_long`, `send_discharges_not_full`) and the unit's
headline claim (`wire_flag_free_of_send`), restated about the extracted
`stuffed_channel.StuffedChannel` methods.

## One proof, over any lawful record

Every theorem quantifies over an extracted queue record `inst`, a model queue `Q` satisfying the
bounded-queue laws, a simulation `hsim` and a functional relation `hfun`, exactly as
`Refinement.lean` does. Each is a corollary of the *unchanged* core theorem at
`SChan (ExtQ S Q inst R)`, the specification channel whose queue is the extracted carrier, with the
laws instance `hsim.boundedQueueLaws hfun`, composed with the per-operation refinements. No proof
here unfolds a queue, a codec or a checksum: the queue is reached through `hsim`, the framing codec,
the varint and the checksum through `Frame.lean`'s refinements, which themselves reach
`stuff::encode_frame`, `stuff::unstuff`, `encode_u32`, `decode_u32` and `crc8` only through their
registered component refinements. `send_refuses_too_long_extracted` unfolds the channel's own `send`
(the refusal happens before any component is called).

## The transparency corollary

`wire_flag_free_extracted` is the theorem `Channel` cannot have, on the extracted side: the bytes
the extracted `encode_stuffed` appends carry the HDLC flag nowhere but at their final position, so a
receiver may scan the wire to the next flag. It is stated here as well as in the model because the
model alone would leave the claim about Lean rather than about the Rust that ships.

## Hypotheses left

* room on the wire, `c.wire.length + 2 * payload.length + 13 ≤ Usize.max`, wherever a frame is
  written (a real extracted `Vec` bound);
* `send_bounded_extracted` alone keeps `send_refines`' overflow hypothesis, because the core
  `send_bounded` assumes no invariant; every other theorem discharges it from `SChanInv`
  (`hovf_of_inv`).

`Instance.lean` beside this file discharges `hsim`, `hfun` and the laws at both extracted queues.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Bridge.channel (ExtQ)
open FramedChannel.Channel (Frame FrameCarrier FrameOK)
open FramedChannel.StuffedChannel (SChan SChanInv encodeStuffed parseStuffed)

/-! ## The transparency corollary, at the extracted encoder -/

/-- TRANSPARENCY at the extracted code: the bytes the extracted `encode_stuffed` appends to the wire
carry the HDLC flag nowhere but at their last position, so a receiver may scan to the next flag.
This is the claim the unstuffed `channel.encode_frame` cannot make --
`lean/FramedChannel/Evidence/Countermodels.lean` refutes the corresponding statement about it in the
kernel. `[EXTRACTED: aeneas + bridge]` -/
theorem wire_flag_free_extracted (payload : Slice Std.U8) (len : Std.U32)
    (out : alloc.vec.Vec Std.U8) (hlen : len.val = payload.val.length)
    (hroom : out.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.encode_stuffed payload len out ⦃ v =>
      ∃ w, bytesOf v.val = bytesOf out.val ++ w ∧
        (∀ b ∈ w.dropLast, b ≠ FramedChannel.Stuff.marker) ∧
        w.getLast? = some FramedChannel.Stuff.marker ⦄ := by
  apply WP.spec_mono (encode_stuffed_refines payload len out hlen hroom)
  intro v hv
  refine ⟨_, hv, ?_, ?_⟩
  · exact FramedChannel.StuffedChannel.wire_flag_free_of_send (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) FramedChannel.Stuff.marker (bitsOf payload.val)
  · exact FramedChannel.StuffedChannel.Transparent.ends_with_flag
      (C := FramedChannel.Stuff.Hdlc) (flag := FramedChannel.Stuff.marker) _

section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)]
  [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hsim hfun

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] hfun in
/-- `SChanInv` discharges `send_refines`' overflow hypothesis: queued plus in-flight is at most the
capacity, which the extracted record reports as a `usize`. -/
theorem hovf_of_inv (m : SChan (ExtQ S Q inst R)) (ps : List Frame)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m ps) :
    (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out).length
      + m.inFlight ≤ Usize.max := by
  obtain ⟨-, -, -, hcap⟩ := hInv
  obtain ⟨q, hq⟩ := m.out.2
  obtain ⟨k, -, hk⟩ := (WP.spec_equiv_exists _ _).mp (hsim.capacity m.out.1 q hq)
  rw [extCapacity_eq hsim m.out q hq, ← hk] at hcap
  have : k.val ≤ Usize.max := by scalar_tac
  omega

/-- `deliver_spec` at the extracted code: delivering the oldest pending frame returns it as `Ok v`,
pushes exactly its carrier onto the specification queue, and keeps the invariant. The parser
divergence is excluded by `SChanInv` (every pending frame is `FrameOK`).
`[EXTRACTED: aeneas + bridge]` -/
theorem deliver_spec_extracted (c : stuffed_channel.StuffedChannel S) (m : SChan (ExtQ S Q inst R))
    (p : Frame) (ps : List Frame) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m (p :: ps)) :
    stuffed_channel.StuffedChannel.deliver inst c ⦃ r c' =>
      ∃ v m', r = .Ok v ∧ bitsOf v.val = p ∧ SChanRel c' m' ∧
        QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out =
          QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out ++
            [FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) p] ∧
        SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) m' ps ⦄ := by
  haveI := hsim.boundedQueueLaws hfun
  obtain ⟨m', hd, hlist, hInv'⟩ := FramedChannel.StuffedChannel.deliver_spec
    (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
    (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) FramedChannel.Stuff.marker m p ps hInv
  have hwire : m.wire = encodeStuffed (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) p ++ (ps.map (encodeStuffed
        (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise))).flatten := by
    rw [hInv.1]; simp
  have hp : FrameOK p := hInv.2.2.1 p (by simp)
  apply WP.spec_mono (deliver_refines hsim c m hR)
  rintro ⟨r, c'⟩ ⟨hok, -⟩
  rcases hok m' hd with ⟨v, p', rest, hr, hparse, hv, hR'⟩ | hwide
  · rw [hwire, FramedChannel.StuffedChannel.parseStuffed_encodeStuffed
      (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      FramedChannel.Stuff.marker p _ hp] at hparse
    simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hparse
    exact ⟨v, m', hr, hv.trans hparse.1.symm, hR', hlist, hInv'⟩
  · rw [hwire] at hwide
    exact absurd hwide (not_declaresWide_encodeStuffed p _ hp)

/-- `send_inv` at the extracted code: a successful extracted `send` keeps the invariant with the
payload appended to the pending frames; a refusal leaves the channel unchanged.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_inv_extracted (c : stuffed_channel.StuffedChannel S) (m : SChan (ExtQ S Q inst R))
    (ps : List Frame) (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m ps)
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c' =>
      (r = .Ok () → ∃ m' : SChan (ExtQ S Q inst R), SChanRel c' m' ∧
        SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
          (E := alloc.vec.Vec Std.U8) m' (ps ++ [bitsOf payload.val])) ∧
      (r = .Err () → c' = c) ⦄ := by
  haveI := hsim.boundedQueueLaws hfun
  apply WP.spec_mono (send_refines hsim hfun c m payload hR (hovf_of_inv hsim m ps hInv) hw)
  rintro ⟨r, c'⟩ ⟨hok, hfail⟩
  cases hs : FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) with
  | ok m' =>
    obtain ⟨hr, hR'⟩ := hok m' hs
    refine ⟨fun _ => ⟨m', hR', FramedChannel.StuffedChannel.send_inv
      (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m' ps _ hInv hs⟩, ?_⟩
    intro h; rw [hr] at h; cases h
  | fail =>
    obtain ⟨hr, hc⟩ := hfail hs
    exact ⟨fun h => (by rw [hr] at h; cases h), fun _ => hc⟩

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] in
/-- `send_bounded` at the extracted code: after a successful extracted `send`, queued plus in-flight
is within the capacity, with no invariant assumed (only `send_refines`' overflow and wire-room
hypotheses). `[EXTRACTED: aeneas + bridge]` -/
theorem send_bounded_extracted (c : stuffed_channel.StuffedChannel S) (m : SChan (ExtQ S Q inst R))
    (payload : Slice Std.U8) (hR : SChanRel c m)
    (hovf : (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out).length +
      m.inFlight ≤ Usize.max)
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c' =>
      r = .Ok () → ∃ m', SChanRel c' m' ∧
        (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out).length
            + m'.inFlight ≤
          QueueModel.capacity (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out ⦄ := by
  apply WP.spec_mono (send_refines hsim hfun c m payload hR hovf hw)
  rintro ⟨r, c'⟩ ⟨hok, hfail⟩ hr
  cases hs : FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) with
  | ok m' =>
    exact ⟨m', (hok m' hs).2, FramedChannel.StuffedChannel.send_bounded
      (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m' _ hs⟩
  | fail =>
    have := (hfail hs).1; rw [hr] at this; cases this

/-- The headline composite at the extracted code: from an extracted channel related to an idle
specification channel, a successful extracted `send` followed by an extracted `deliver` returns
`Ok v` whose bytes are exactly the payload's, the related specification queue grows by exactly that
frame, and the channel is idle again. The one hypothesis beyond the relation is room on the wire.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_extracted (c : stuffed_channel.StuffedChannel S) (m : SChan (ExtQ S Q inst R))
    (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m [])
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c1 =>
      r = .Ok () →
        stuffed_channel.StuffedChannel.deliver inst c1 ⦃ r2 c2 =>
          ∃ v m2, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧ SChanRel c2 m2 ∧
            QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m2.out =
              QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out ++
                [FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) (bitsOf payload.val)] ∧
            SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
              (E := alloc.vec.Vec Std.U8) m2 [] ⦄ ⦄ := by
  haveI := hsim.boundedQueueLaws hfun
  apply WP.spec_mono (send_refines hsim hfun c m payload hR (hovf_of_inv hsim m [] hInv) hw)
  rintro ⟨r, c1⟩ ⟨hok, hfail⟩ hr
  cases hs : FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) with
  | ok m1 =>
    have hR1 := (hok m1 hs).2
    have hInv1 := FramedChannel.StuffedChannel.send_inv (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m1 [] _ hInv hs
    have hout := FramedChannel.StuffedChannel.send_out (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m1 _ hs
    apply WP.spec_mono (deliver_spec_extracted hsim hfun c1 m1 (bitsOf payload.val) [] hR1 hInv1)
    rintro ⟨r2, c2⟩ ⟨v, m2, hr2, hv, hR2, hlist, hInv2⟩
    exact ⟨v, m2, hr2, hv, hR2, by rw [hlist, hout], hInv2⟩
  | fail =>
    have := (hfail hs).1; rw [hr] at this; cases this

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] in
/-- `send_refuses_too_long` at the extracted code: a payload longer than `u32::MAX` bytes is refused
with the channel unchanged, whatever the queue holds. No wire-room hypothesis: the refusal happens
before the frame is written. `[EXTRACTED: aeneas + bridge]` -/
theorem send_refuses_too_long_extracted (c : stuffed_channel.StuffedChannel S)
    (m : SChan (ExtQ S Q inst R)) (ps : List Frame) (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m ps)
    (hlong : U32.max < payload.val.length) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r c' => r = .Err () ∧ c' = c ⦄ := by
  have hovf := hovf_of_inv hsim m ps hInv
  obtain ⟨hout, -, hfl⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hout ▸ hq
  rw [extToList_eq (T := alloc.vec.Vec Std.U8) hfun m.out q hq] at hovf
  unfold stuffed_channel.StuffedChannel.send
  step with hsim.len c.out q hq' as ⟨n, hn⟩
  have hadd : n.val + c.in_flight.val ≤ Usize.max := by rw [hn, hfl]; exact hovf
  step*
  step with hsim.capacity c.out q hq' as ⟨k, hk⟩
  have hl : U32.max < payload.len.val := by simp only [Slice.len_val]; exact hlong
  step*

/-- `send_discharges_not_full` at the extracted code: when the extracted `send` succeeds, the
extracted queue record's own `is_full` reports `false` on the queue it saw.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_discharges_not_full_extracted (c : stuffed_channel.StuffedChannel S)
    (m : SChan (ExtQ S Q inst R)) (ps : List Frame) (payload : Slice Std.U8) (hR : SChanRel c m)
    (hInv : SChanInv (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (E := alloc.vec.Vec Std.U8) m ps)
    (hw : c.wire.val.length + 2 * payload.val.length + 13 ≤ Usize.max) :
    stuffed_channel.StuffedChannel.send inst c payload ⦃ r _ =>
      r = .Ok () → inst.is_full c.out ⦃ b => b = false ⦄ ⦄ := by
  haveI := hsim.boundedQueueLaws hfun
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hR.1 ▸ hq
  apply WP.spec_mono (send_refines hsim hfun c m payload hR (hovf_of_inv hsim m ps hInv) hw)
  rintro ⟨r, c'⟩ ⟨hok, hfail⟩ hr
  cases hs : FramedChannel.StuffedChannel.send (C := FramedChannel.Stuff.Hdlc)
      (K := FramedChannel.Crc8.Bitwise) (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) with
  | ok m' =>
    have hnf := FramedChannel.StuffedChannel.send_discharges_not_full
      (C := FramedChannel.Stuff.Hdlc) (K := FramedChannel.Crc8.Bitwise)
      (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m' _ hs
    rw [extFull_eq hsim m.out q hq] at hnf
    apply WP.spec_mono (hsim.is_full c.out q hq')
    intro b hb
    rw [hb]
    simpa using hnf
  | fail =>
    have := (hfail hs).1; rw [hr] at this; cases this

end

end FramedChannel.Bridge.stuffed_channel

#print axioms FramedChannel.Bridge.stuffed_channel.wire_flag_free_extracted
#print axioms FramedChannel.Bridge.stuffed_channel.hovf_of_inv
#print axioms FramedChannel.Bridge.stuffed_channel.deliver_spec_extracted
#print axioms FramedChannel.Bridge.stuffed_channel.send_inv_extracted
#print axioms FramedChannel.Bridge.stuffed_channel.send_bounded_extracted
#print axioms FramedChannel.Bridge.stuffed_channel.send_deliver_extracted
#print axioms FramedChannel.Bridge.stuffed_channel.send_refuses_too_long_extracted
#print axioms FramedChannel.Bridge.stuffed_channel.send_discharges_not_full_extracted
