-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Channel.Refinement

/-!
# Bridge/Channel/Composite: the channel's composition theorems, at the extracted code

`[EXTRACTED: aeneas + bridge]` -- the composition theorems of
`lean/FramedChannel/Composition/Channel/Theorems.lean` (`send_deliver`, `deliver_spec`, `send_inv`,
`send_bounded`, `send_refuses_too_long`, `send_discharges_not_full`), restated about the extracted
`channel.Channel` methods.

## One proof, over any lawful record

Every theorem quantifies over an extracted queue record `inst`, a model queue `Q` satisfying the
bounded-queue laws, a simulation `hsim` and a functional relation `hfun`, exactly as
`Refinement.lean` does. Each is a corollary of the *unchanged* core theorem at
`Chan (ExtQ S Q inst R)`, the specification channel whose queue is the extracted carrier, with
the laws instance `hsim.boundedQueueLaws hfun`, composed with the per-operation refinements. No
proof here unfolds a queue, a codec or a checksum: the queue is reached through `hsim`, the codec
and checksum through `Frame.lean`'s refinements, which themselves reach `encode_u32`,
`decode_u32` and `crc8` only through their registered component refinements.
`send_refuses_too_long_extracted` unfolds the channel's own `send` (the refusal happens before any
component is called).

## Hypotheses left

* room on the wire, `c.wire.length + payload.length + 7 ≤ Usize.max`, wherever a frame is
  written (a real extracted `Vec` bound);
* `send_bounded_extracted` alone keeps `send_refines`' overflow hypothesis, because the core
  `send_bounded` assumes no invariant; every other theorem discharges it from `ChanInv`
  (`hovf_of_inv`).

`Instance.lean` beside this file discharges `hsim`, `hfun` and the laws at both extracted queues.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Chan FrameCarrier FrameOK ChanInv encodeFrame parseFrame)

/-- A frame the channel accepts never declares a wide length. -/
theorem not_declaresWide_encodeFrame (p rest : List (BitVec 8)) (hp : FrameOK p) :
    ¬ DeclaresWideLength (encodeFrame p ++ rest) := by
  rintro ⟨rest', n, rem, hw, hd, hn⟩
  simp only [encodeFrame, List.cons_append, List.cons.injEq] at hw
  obtain ⟨-, hr⟩ := hw
  rw [← hr, decode_encodeFrame_tail p rest hp] at hd
  simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hd
  simp only [FrameOK] at hp
  omega

section
variable {S Q : Type} [QueueModel Q (alloc.vec.Vec Std.U8)] [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)]
  {inst : queue.BoundedQueue S (alloc.vec.Vec Std.U8)} {R : S → Q → Prop}
  (hsim : QueueSim S Q (alloc.vec.Vec Std.U8) inst R)
  (hfun : ∀ s q q', R s q → R s q' → q = q')
include hsim hfun

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] hfun in
/-- `ChanInv` discharges `send_refines`' overflow hypothesis: queued plus in-flight is at most the
capacity, which the extracted record reports as a `usize`. -/
theorem hovf_of_inv (m : Chan (ExtQ S Q inst R)) (ps : List FramedChannel.Channel.Frame)
    (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m ps) :
    (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out).length + m.inFlight ≤ Usize.max := by
  obtain ⟨-, -, -, hcap⟩ := hInv
  obtain ⟨q, hq⟩ := m.out.2
  obtain ⟨k, -, hk⟩ := (WP.spec_equiv_exists _ _).mp (hsim.capacity m.out.1 q hq)
  rw [extCapacity_eq hsim m.out q hq, ← hk] at hcap
  have : k.val ≤ Usize.max := by scalar_tac
  omega

/-- `deliver_spec` at the extracted code: delivering the oldest pending frame returns it as `Ok v`,
pushes exactly its carrier onto the specification queue, and keeps the invariant. The parser
divergence is excluded by `ChanInv` (every pending frame is `FrameOK`).
`[EXTRACTED: aeneas + bridge]` -/
theorem deliver_spec_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (p : FramedChannel.Channel.Frame) (ps : List FramedChannel.Channel.Frame)
    (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m (p :: ps)) :
    channel.Channel.deliver inst c ⦃ r c' =>
      ∃ v m', r = .Ok v ∧ bitsOf v.val = p ∧ ChanRel c' m' ∧
        QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out =
          QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out ++
            [FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) p] ∧
        ChanInv (E := alloc.vec.Vec Std.U8) m' ps ⦄ := by
  haveI := hsim.boundedQueueLaws hfun
  obtain ⟨m', hd, hlist, hInv'⟩ := FramedChannel.Channel.deliver_spec (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m p ps hInv
  have hwire : m.wire = encodeFrame p ++ (ps.map encodeFrame).flatten := by
    rw [hInv.1]; simp
  have hp : FrameOK p := hInv.2.2.1 p (by simp)
  apply WP.spec_mono (deliver_refines hsim c m hR)
  rintro ⟨r, c'⟩ ⟨hok, -⟩
  rcases hok m' hd with ⟨v, p', rest, hr, hparse, hv, hR'⟩ | hwide
  · rw [hwire, FramedChannel.Channel.parseFrame_encodeFrame p _ hp] at hparse
    simp only [FramedChannel.Result.ok.injEq, Prod.mk.injEq] at hparse
    exact ⟨v, m', hr, hv.trans hparse.1.symm, hR', hlist, hInv'⟩
  · rw [hwire] at hwide
    exact absurd hwide (not_declaresWide_encodeFrame p _ hp)

/-- `send_inv` at the extracted code: a successful extracted `send` keeps the invariant with the
payload appended to the pending frames; a refusal leaves the channel unchanged.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_inv_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (ps : List FramedChannel.Channel.Frame) (payload : Slice Std.U8)
    (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m ps)
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r c' =>
      (r = .Ok () → ∃ m' : Chan (ExtQ S Q inst R), ChanRel c' m' ∧ ChanInv (E := alloc.vec.Vec Std.U8) m' (ps ++ [bitsOf payload.val])) ∧
      (r = .Err () → c' = c) ⦄ := by
  haveI := hsim.boundedQueueLaws hfun
  apply WP.spec_mono (send_refines hsim hfun c m payload hR (hovf_of_inv hsim m ps hInv) hw)
  rintro ⟨r, c'⟩ ⟨hok, hfail⟩
  cases hs : FramedChannel.Channel.send (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) with
  | ok m' =>
    obtain ⟨hr, hR'⟩ := hok m' hs
    refine ⟨fun _ => ⟨m', hR', FramedChannel.Channel.send_inv (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m' ps _ hInv hs⟩, ?_⟩
    intro h; rw [hr] at h; cases h
  | fail =>
    obtain ⟨hr, hc⟩ := hfail hs
    exact ⟨fun h => (by rw [hr] at h; cases h), fun _ => hc⟩

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] in
/-- `send_bounded` at the extracted code: after a successful extracted `send`, queued plus in-flight
is within the capacity, with no invariant assumed (only `send_refines`' overflow and wire-room
hypotheses). `[EXTRACTED: aeneas + bridge]` -/
theorem send_bounded_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (payload : Slice Std.U8) (hR : ChanRel c m)
    (hovf : (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out).length +
      m.inFlight ≤ Usize.max)
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r c' =>
      r = .Ok () → ∃ m', ChanRel c' m' ∧
        (QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out).length + m'.inFlight ≤
          QueueModel.capacity (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m'.out ⦄ := by
  apply WP.spec_mono (send_refines hsim hfun c m payload hR hovf hw)
  rintro ⟨r, c'⟩ ⟨hok, hfail⟩ hr
  cases hs : FramedChannel.Channel.send (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) with
  | ok m' =>
    exact ⟨m', (hok m' hs).2, FramedChannel.Channel.send_bounded (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m' _ hs⟩
  | fail =>
    have := (hfail hs).1; rw [hr] at this; cases this

/-- The headline composite at the extracted code: from an extracted channel related to an idle
specification channel, a successful extracted `send` followed by an extracted `deliver` returns
`Ok v` whose bytes are exactly the payload's, the related specification queue grows by exactly that
frame, and the channel is idle again. The one hypothesis beyond the relation is room on the wire.
Proved from the component laws alone, through the core `send_deliver`'s ingredients.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_deliver_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (payload : Slice Std.U8) (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m [])
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r c1 =>
      r = .Ok () →
        channel.Channel.deliver inst c1 ⦃ r2 c2 =>
          ∃ v m2, r2 = .Ok v ∧ bitsOf v.val = bitsOf payload.val ∧ ChanRel c2 m2 ∧
            QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m2.out =
              QueueModel.toList (Q := ExtQ S Q inst R) (α := alloc.vec.Vec Std.U8) m.out ++
                [FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) (bitsOf payload.val)] ∧
            ChanInv (E := alloc.vec.Vec Std.U8) m2 [] ⦄ ⦄ := by
  haveI := hsim.boundedQueueLaws hfun
  apply WP.spec_mono (send_refines hsim hfun c m payload hR (hovf_of_inv hsim m [] hInv) hw)
  rintro ⟨r, c1⟩ ⟨hok, hfail⟩ hr
  cases hs : FramedChannel.Channel.send (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) with
  | ok m1 =>
    have hR1 := (hok m1 hs).2
    have hInv1 := FramedChannel.Channel.send_inv (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m1 [] _ hInv hs
    have hout := FramedChannel.Channel.send_out (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m1 _ hs
    apply WP.spec_mono (deliver_spec_extracted hsim hfun c1 m1 (bitsOf payload.val) [] hR1 hInv1)
    rintro ⟨r2, c2⟩ ⟨v, m2, hr2, hv, hR2, hlist, hInv2⟩
    exact ⟨v, m2, hr2, hv, hR2, by rw [hlist, hout], hInv2⟩
  | fail =>
    have := (hfail hs).1; rw [hr] at this; cases this

omit [BoundedQueueLaws Q (alloc.vec.Vec Std.U8)] in
/-- `send_refuses_too_long` at the extracted code: a payload longer than `u32::MAX` bytes is refused
with the channel unchanged, whatever the queue holds. No wire-room hypothesis: the refusal happens
before the frame is written. (Such a payload exists only where `usize` is 64 bits; the statement is
uniform.) `[EXTRACTED: aeneas + bridge]` -/
theorem send_refuses_too_long_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (ps : List FramedChannel.Channel.Frame) (payload : Slice Std.U8)
    (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m ps)
    (hlong : U32.max < payload.val.length) :
    channel.Channel.send inst c payload ⦃ r c' => r = .Err () ∧ c' = c ⦄ := by
  have hovf := hovf_of_inv hsim m ps hInv
  obtain ⟨hout, -, hfl⟩ := hR
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hout ▸ hq
  rw [extToList_eq (T := alloc.vec.Vec Std.U8) hfun m.out q hq] at hovf
  unfold channel.Channel.send
  step with hsim.len c.out q hq' as ⟨n, hn⟩
  have hadd : n.val + c.in_flight.val ≤ Usize.max := by rw [hn, hfl]; exact hovf
  step*
  step with hsim.capacity c.out q hq' as ⟨k, hk⟩
  have hl : U32.max < payload.len.val := by simp only [Slice.len_val]; exact hlong
  step*

/-- `send_discharges_not_full` at the extracted code: when the extracted `send` succeeds, the
extracted queue record's own `is_full` reports `false` on the queue it saw.
`[EXTRACTED: aeneas + bridge]` -/
theorem send_discharges_not_full_extracted (c : channel.Channel S) (m : Chan (ExtQ S Q inst R))
    (ps : List FramedChannel.Channel.Frame) (payload : Slice Std.U8)
    (hR : ChanRel c m) (hInv : ChanInv (E := alloc.vec.Vec Std.U8) m ps)
    (hw : c.wire.val.length + payload.val.length + 7 ≤ Usize.max) :
    channel.Channel.send inst c payload ⦃ r _ =>
      r = .Ok () → inst.is_full c.out ⦃ b => b = false ⦄ ⦄ := by
  haveI := hsim.boundedQueueLaws hfun
  obtain ⟨q, hq⟩ := m.out.2
  have hq' : R c.out q := hR.1 ▸ hq
  apply WP.spec_mono (send_refines hsim hfun c m payload hR (hovf_of_inv hsim m ps hInv) hw)
  rintro ⟨r, c'⟩ ⟨hok, hfail⟩ hr
  cases hs : FramedChannel.Channel.send (E := alloc.vec.Vec Std.U8) m (bitsOf payload.val) with
  | ok m' =>
    have hnf := FramedChannel.Channel.send_discharges_not_full (ExtQ S Q inst R) (alloc.vec.Vec Std.U8) m m' _ hs
    rw [extFull_eq hsim m.out q hq] at hnf
    apply WP.spec_mono (hsim.is_full c.out q hq')
    intro b hb
    rw [hb]
    simpa using hnf
  | fail =>
    have := (hfail hs).1; rw [hr] at this; cases this

end

end FramedChannel.Bridge.channel

#print axioms FramedChannel.Bridge.channel.not_declaresWide_encodeFrame
#print axioms FramedChannel.Bridge.channel.hovf_of_inv
#print axioms FramedChannel.Bridge.channel.deliver_spec_extracted
#print axioms FramedChannel.Bridge.channel.send_inv_extracted
#print axioms FramedChannel.Bridge.channel.send_bounded_extracted
#print axioms FramedChannel.Bridge.channel.send_deliver_extracted
#print axioms FramedChannel.Bridge.channel.send_refuses_too_long_extracted
#print axioms FramedChannel.Bridge.channel.send_discharges_not_full_extracted
