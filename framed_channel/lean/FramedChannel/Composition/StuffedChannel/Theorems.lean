-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Composition.StuffedChannel.Defs
import FramedChannel.Composition.Channel.Theorems
import FramedChannel.Model.Varint.Theorems

/-!
# Composition/StuffedChannel/Theorems: the transparent composite, proved from three interfaces

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/stuffed_channel.rs`. `send`
builds one frame body (varint length, payload, check byte) after the channel's own capacity check
`queued + in_flight < capacity` and its length check `payload.len() < 2 ^ 32`, and writes that body
onto the wire through the framing codec; `deliver` reads one framed body back off the wire, checks
the digest and pushes the payload onto the output queue. The Rust `send` and `deliver` are the same
two operations with the same guards and the same single failure case, so this is a model of that
file at the operation level.

## The theorem `Channel` cannot have

`wire_flag_free_of_send`: no byte the channel writes, other than a frame terminator, is the flag.
That is what makes the wire scannable, and it is exactly what the unstuffed `Channel` lacks --
`Evidence/Countermodels.lean` refutes the corresponding claim about `Channel.encodeFrame` in the
kernel, at the one-byte payload `[marker]`.

The round trip `parseStuffed_encodeStuffed` is *not* that distinguishing claim. It holds at every
payload, marker-bearing ones included, with no marker-freedom hypothesis -- but so does
`Channel.parseFrame_encodeFrame`, because a varint length prefix already tells the receiver how
many bytes to take. What stuffing buys is the marker-free wire, not the round trip.

## Composition: three interfaces, reached generically

* the output queue through `Spec/Queue.lean` alone (`QueueModel`, `BoundedQueueLaws`);
* the framing codec through `Spec/Codec.lean`'s L0 `CodecModel` plus the composition-layer bundle
  `Transparent` of `Defs.lean` -- **not** `CodecLaws`, which is too weak twice over (its `Dom` at
  `Stuff` caps payloads at 255 bytes, and its `round_trip` gives residual `[]` only). `Defs.lean`'s
  docstring records that in full;
* the checksum through `Spec/Checksum.lean`'s L0 `ChecksumModel`. No `ChecksumLaws` law is used:
  the round trip needs only that both sides apply the same `digest`.

`Channel` reaches one interface generically; this composite reaches three. That is the strength of
the claim, and the manifest states it that way rather than as a composition of `CodecLaws` and
`ChecksumLaws`.

`Varint` is the one component reached monomorphically, through `Varint.varint_roundtrip` -- exactly
as `Channel` reaches it, and for the same reason: the length prefix's codec is fixed by the wire
format, not a parameter of the composite.

## Scope

* This module imports no queue model and no `Model/Stuff/Theorems`, so the genericity claim is
  mechanically visible: nothing here can appeal to how HDLC stuffing actually works. The
  `Transparent` instance at `Stuff.Hdlc` lives in `Composition/StuffedChannel/Instances.lean`,
  which is where the composition layer meets the model layer.
* `send_out` is a supporting lemma, not a registered row -- `Channel` does not register its
  analogue either.
* Corruption and concurrency are out of scope; the wire is delivered as sent.
* Error agreement against the extracted code is a bridge-level obligation, discharged in
  `aeneas/FramedChannelAeneas/Bridge/StuffedChannel/`.
-/

namespace FramedChannel.StuffedChannel

open FramedChannel
open FramedChannel.Channel (Byte Frame FrameOK FrameCarrier lenBytes toNat_lenBytes decodeF_append
  ofNat_toNat_map)

section
variable {C K : Type} [CodecModel C (List Nat)] [ChecksumModel K]

/-- Transparency round trip: one frame recovered off a stuffed wire, at every payload including one
containing the flag byte, with no marker-freedom hypothesis. Composed from the codec's
`decode_append` and `Varint.varint_roundtrip`. `[PROVED: kernel]` -/
theorem parseStuffed_encodeStuffed (flag : Nat) [Transparent C flag]
    (p : Frame) (rest : List Nat) (hp : p.length < 2 ^ 32) :
    parseStuffed (C := C) (K := K) (encodeStuffed (C := C) (K := K) p ++ rest)
      = .ok (p, rest) := by
  rung manual =>
    have hstuff := Transparent.decode_append (C := C) (flag := flag) (body (K := K) p) rest
    have hv := Varint.varint_roundtrip p.length hp
    have hd := decodeF_append 5 1 0 p.length (Varint.encode p.length)
      ((p ++ [ChecksumModel.digest (C := K) p]).map BitVec.toNat) hv
    have hbody : body (K := K) p
        = Varint.encode p.length ++ (p ++ [ChecksumModel.digest (C := K) p]).map BitVec.toNat := by
      simp only [body, List.map_append, toNat_lenBytes]
    simp only [parseStuffed, encodeStuffed]
    rw [hstuff, hbody]
    simp only [Varint.decode] at hd ⊢
    rw [hd]
    simp only [ofNat_toNat_map]
    simp

/-- TRANSPARENCY, the theorem `Channel` cannot have: every byte the channel has written other than
the frame terminator is not the flag, so a receiver may scan to the next flag. `[PROVED: kernel]` -/
theorem wire_flag_free_of_send (flag : Nat) [Transparent C flag] (p : Frame) :
    ∀ b ∈ (encodeStuffed (C := C) (K := K) p).dropLast, b ≠ flag := by
  rung retrieval => exact Transparent.body_flag_free (C := C) (flag := flag) (body (K := K) p)

/-- `send` does not touch the output queue. A supporting lemma, not a registered row.
`[PROVED: kernel]` -/
theorem send_out (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c c' : SChan Q) (p : Frame)
    (h : send (C := C) (K := K) (E := E) c p = .ok c') : c'.out = c.out := by
  unfold send at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Result.ok.injEq] at h
      subst h
      rfl

/-- The capacity check of `send` discharges `push`'s not-full assumption. `[PROVED: kernel]` -/
theorem send_discharges_not_full (Q E : Type) [FrameCarrier E] [QueueModel Q E]
    [BoundedQueueLaws Q E] (c c' : SChan Q) (p : Frame)
    (h : send (C := C) (K := K) (E := E) c p = .ok c') :
    ¬ QueueModel.full (Q := Q) (α := E) c.out := by
  rung retrieval =>
    simp only [send] at h
    grind [BoundedQueueLaws.not_full_of_lt]

/-- Bounds: after a successful `send`, queued plus in-flight is still within the capacity. It holds
with no `SChanInv` assumption and from the L0 interface alone: `send`'s own guard is what makes
`deliver`'s push total. `[PROVED: kernel]` -/
theorem send_bounded (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c c' : SChan Q) (p : Frame)
    (h : send (C := C) (K := K) (E := E) c p = .ok c') :
    (QueueModel.toList (Q := Q) (α := E) c'.out).length + c'.inFlight ≤
      QueueModel.capacity (Q := Q) (α := E) c'.out := by
  rung grind =>
    simp only [send] at h
    grind

/-- `send` refuses every payload that is not `FrameOK`, i.e. of `2 ^ 32` bytes or more, whatever the
capacity: the Lean statement of the Rust length guard. `[PROVED: kernel]` -/
theorem send_refuses_too_long (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c : SChan Q)
    (p : Frame) (hp : ¬ FrameOK p) : send (C := C) (K := K) (E := E) c p = .fail := by
  rung simp => simp_all [send, FrameOK]

/-- `send` preserves the channel invariant, adding the frame to the pending list. The new frame's
`FrameOK` comes from `send`'s own length check, so there is no caller hypothesis on `p`.
`[PROVED: kernel]` -/
theorem send_inv (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c c' : SChan Q) (ps : List Frame) (p : Frame)
    (hInv : SChanInv (C := C) (K := K) (E := E) c ps)
    (h : send (C := C) (K := K) (E := E) c p = .ok c') :
    SChanInv (C := C) (K := K) (E := E) c' (ps ++ [p]) := by
  rung grind =>
    grind [FramedChannel.Channel.FrameOK, FramedChannel.Channel.lenBytes,
      FramedChannel.StuffedChannel.SChanInv, FramedChannel.StuffedChannel.body,
      FramedChannel.StuffedChannel.encodeStuffed, FramedChannel.StuffedChannel.send,
      FramedChannel.Varint.encode, FramedChannel.Varint.encodeF]

/-- The composite: delivering the oldest pending frame pushes exactly that frame onto the abstract
queue and keeps the invariant. Proved from the queue laws, the codec's `Transparent` bundle and the
checksum interface only. `[PROVED: kernel]` -/
theorem deliver_spec (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (flag : Nat) [Transparent C flag] (c : SChan Q) (p : Frame) (ps : List Frame)
    (hInv : SChanInv (C := C) (K := K) (E := E) c (p :: ps)) :
    ∃ c', deliver (C := C) (K := K) (E := E) c = .ok c' ∧
      QueueModel.toList (Q := Q) (α := E) c'.out =
        QueueModel.toList (Q := Q) (α := E) c.out ++ [FrameCarrier.ofFrame (E := E) p] ∧
      SChanInv (C := C) (K := K) (E := E) c' ps := by
  rung manual =>
    obtain ⟨hw, hf, hps, hcap⟩ := hInv
    have hp : FrameOK p := hps p (by simp)
    have hnf : ¬ QueueModel.full (Q := Q) (α := E) c.out := by
      apply BoundedQueueLaws.not_full_of_lt
      simp only [List.length_cons] at hf
      omega
    obtain ⟨q', hq', hlist⟩ := BoundedQueueLaws.push_law c.out (FrameCarrier.ofFrame (E := E) p) hnf
    have hparse : parseStuffed (C := C) (K := K) c.wire
        = .ok (p, (ps.map (encodeStuffed (C := C) (K := K))).flatten) := by
      rw [hw]
      simp only [List.map_cons, List.flatten_cons]
      exact parseStuffed_encodeStuffed (C := C) (K := K) flag p _ hp
    refine ⟨{ out := q', wire := (ps.map (encodeStuffed (C := C) (K := K))).flatten,
              inFlight := c.inFlight - 1 }, ?_, hlist, ?_⟩
    · unfold deliver
      rw [hparse]
      simp only [hq']
    · have hc := BoundedQueueLaws.push_capacity c.out (FrameCarrier.ofFrame (E := E) p) q' hq'
      refine ⟨rfl, ?_, fun x hx => hps x (by simp [hx]), ?_⟩
      · simp only [List.length_cons] at hf; simp only; omega
      · simp only [List.length_cons] at hf
        simp only [hlist, List.length_append, List.length_singleton, hc]
        omega

/-- The headline composite: from an idle channel, a successful `send` then `deliver` pushes exactly
`p` onto the abstract queue and returns the channel to idle. No `FrameOK p` hypothesis: `send`
refuses every payload outside it. `[PROVED: kernel]` -/
theorem send_deliver (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (flag : Nat) [Transparent C flag] (c c' : SChan Q) (p : Frame)
    (hInv : SChanInv (C := C) (K := K) (E := E) c [])
    (h : send (C := C) (K := K) (E := E) c p = .ok c') :
    ∃ c'', deliver (C := C) (K := K) (E := E) c' = .ok c'' ∧
      QueueModel.toList (Q := Q) (α := E) c''.out =
        QueueModel.toList (Q := Q) (α := E) c.out ++ [FrameCarrier.ofFrame (E := E) p] ∧
      SChanInv (C := C) (K := K) (E := E) c'' [] := by
  rung manual =>
    have hInv' : SChanInv (C := C) (K := K) (E := E) c' [p] := send_inv Q E c c' [] p hInv h
    have hout := send_out (C := C) (K := K) Q E c c' p h
    obtain ⟨c'', hd, hlist, hInv''⟩ := deliver_spec Q E flag c' p [] hInv'
    exact ⟨c'', hd, by rw [hlist, hout], hInv''⟩

end

#print axioms parseStuffed_encodeStuffed
#print axioms wire_flag_free_of_send
#print axioms send_out
#print axioms send_discharges_not_full
#print axioms send_bounded
#print axioms send_refuses_too_long
#print axioms send_inv
#print axioms deliver_spec
#print axioms send_deliver

end FramedChannel.StuffedChannel
