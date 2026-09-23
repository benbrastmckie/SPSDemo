-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Composition.Channel.Defs
import FramedChannel.Model.Varint.Theorems
import FramedChannel.Model.Crc8.Theorems

/-!
# Composition/Channel/Theorems: the composite, proved from the component theorems

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/channel.rs`. `send` writes
one frame onto the wire (marker, varint length, payload, CRC-8) after the channel's own capacity
check `queued + in_flight < capacity` and its length check `payload.len() < 2 ^ 32`; `deliver`
parses one frame off the wire and pushes it onto the output queue. The Rust `send` and `deliver`
are the same two operations with the same guards and the same single failure case, so this is a
model of that file at the operation level.

## What `send = push ∘ checksum ∘ encode` means here

The `∘` is shorthand: `push` is curried over the queue and returns a `Result`, so the three
components do not compose as plain functions. Precisely:

* encode and checksum compose inside `encodeFrame p = marker :: lenBytes p.length ++ p ++
  [crc8Bits p]`. Its round trip `parseFrame_encodeFrame` is derived from `Varint.varint_roundtrip`
  (through `decodeF_append`), and the table-driven encoder agrees with it by
  `Crc8.crc8_table_eq_bits` (`encodeFrameTable_eq`);
* push enters through the Kleisli chain `send c p >>= deliver`: `send_deliver` states that the
  chain pushes exactly `p` onto the abstract queue, and `push_law`'s not-full assumption is
  discharged by `send`'s capacity check through `not_full_of_lt` (`send_discharges_not_full`).

## Substitution and inheritance

`Chan Q` is generic over any `[FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]`: the queue
holds elements of type `E`, and `FrameCarrier.ofFrame` says how a delivered frame becomes one. At
`E := Frame` the carrier is the identity, which is the channel of the hand models. Every channel
theorem is proved from the six laws only: none opens `RingBuffer` or `VQ`, and this module does
not even import them (the composition layer depends on `Spec/Queue.lean`, never on a queue model;
`check.sh` enforces that import rule). `Composition/Channel/Instances.lean`'s `deliver_spec_RB` and
`deliver_spec_VQ` then use `deliver_spec` unchanged at both queues -- proved once, it holds at
every instance. `rust/src/channel.rs` realizes the same substitution executably.

## Scope

* This module is a hand-written model. The Aeneas extraction of `channel.rs` is related to it
  in the bridge package (`aeneas/FramedChannelAeneas/Bridge/Channel/`), which instantiates `Chan`
  at `E := alloc.vec.Vec Std.U8`, the element type the extracted queues hold. That is why the
  element type is a parameter here: no lawful `QueueModel _ Frame` view of a `Vec` queue exists,
  since a frame longer than `Usize.max` has no `Vec`.
* `deliver`'s failure is `.fail` in both directions. The composite theorems show the queue-refusal
  branch is unreachable for frames this channel sent.
* Corruption and concurrency are out of scope; the wire is delivered as sent.
* The parser accepts any length below `2 ^ 32` (`FrameOK`), and `parse_frame` accepts whatever
  `decode_u32` returns, so the two agree on the admitted domain. `send` refuses a payload of
  `2 ^ 32` bytes or more on both sides (`send_refuses_too_long`), so every frame the channel puts
  on the wire is `FrameOK`; the Rust `send` passes `encode_frame` the checked `u32` length.
-/

namespace FramedChannel.Channel

open FramedChannel

/-- The varint decoder ignores what follows a complete encoding. `[PROVED: kernel]` -/
theorem decodeF_append (f : Nat) : ∀ (m acc v : Nat) (bs rest : List Nat),
    Varint.decodeF f m acc bs = .ok (v, []) →
    Varint.decodeF f m acc (bs ++ rest) = .ok (v, rest) := by
  induction f with
  | zero => intro m acc v bs rest h; cases h
  | succ f ih =>
    intro m acc v bs rest h
    cases bs with
    | nil => cases h
    | cons b bs =>
      simp only [Varint.decodeF] at h
      split at h
      · rename_i hb
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [Varint.decodeF, hb]
      · rename_i hb
        simp only [List.cons_append, Varint.decodeF, hb, ↓reduceIte]
        exact ih _ _ _ _ _ h

/-- The length bytes read back as the varint encoding (every emitted byte is below 256).
`[PROVED: kernel]` -/
theorem toNat_lenBytes (n : Nat) : (lenBytes n).map BitVec.toNat = Varint.encode n := by
  simp only [lenBytes, List.map_map]
  conv => rhs; rw [← List.map_id (Varint.encode n)]
  apply List.map_congr_left
  intro b hb
  have := Varint.encodeF_bytes_lt 5 n b hb
  simp [Nat.mod_eq_of_lt this]

/-- Bytes survive a `toNat`/`ofNat` round trip. -/
theorem ofNat_toNat_map (bs : List Byte) :
    (bs.map BitVec.toNat).map (BitVec.ofNat 8) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, ih, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Round trip of one frame under the idealized parser, composed from `varint_roundtrip`.
`[PROVED: kernel]` -/
theorem parseFrame_encodeFrame (p : Frame) (rest : List Byte) (hp : p.length < 2 ^ 32) :
    parseFrame (encodeFrame p ++ rest) = .ok (p, rest) := by
  rung manual =>
    have hv := Varint.varint_roundtrip p.length hp
    have hd := decodeF_append 5 1 0 p.length (Varint.encode p.length)
      ((p ++ [Crc8.crc8Bits p] ++ rest).map BitVec.toNat) hv
    have hmap : (lenBytes p.length ++ (p ++ [Crc8.crc8Bits p]) ++ rest).map BitVec.toNat =
        Varint.encode p.length ++ (p ++ [Crc8.crc8Bits p] ++ rest).map BitVec.toNat := by
      simp only [List.map_append, toNat_lenBytes, List.append_assoc]
    simp only [encodeFrame, List.cons_append, parseFrame, ↓reduceIte]
    rw [hmap]
    simp only [Varint.decode] at hd ⊢
    rw [hd]
    simp only [ofNat_toNat_map]
    simp

/-- The equivalence `crc8_table ≃ crc8` entering the frame encoder. `[PROVED: kernel]` -/
theorem encodeFrameTable_eq (p : Frame) : encodeFrameTable p = encodeFrame p := by
  rung retrieval => simp only [encodeFrameTable, encodeFrame, Crc8.crc8_table_eq_bits]

/-- `send` does not touch the output queue. `[PROVED: kernel]` -/
theorem send_out (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c c' : Chan Q) (p : Frame)
    (h : send (E := E) c p = .ok c') : c'.out = c.out := by
  unfold send at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Result.ok.injEq] at h
      subst h
      rfl

/-- The capacity check of `send` discharges `push`'s not-full assumption. `[PROVED: kernel]` -/
theorem send_discharges_not_full (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c c' : Chan Q) (p : Frame) (h : send (E := E) c p = .ok c') :
    ¬ QueueModel.full (Q := Q) (α := E) c.out := by
  rung retrieval =>
    simp only [send] at h
    grind [BoundedQueueLaws.not_full_of_lt]

/-- Bounds: after a successful `send`, queued plus in-flight is still within the capacity. This is
what the composite needs from `send`, and it holds with no `ChanInv` assumption and from the L0
interface alone: `send`'s own guard is what makes `deliver`'s push total. `[PROVED: kernel]` -/
theorem send_bounded (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c c' : Chan Q) (p : Frame)
    (h : send (E := E) c p = .ok c') :
    (QueueModel.toList (Q := Q) (α := E) c'.out).length + c'.inFlight ≤
      QueueModel.capacity (Q := Q) (α := E) c'.out := by
  rung grind =>
    simp only [send] at h
    grind

/-- `send` preserves the channel invariant, adding the frame to the pending list. The new frame's
`FrameOK` comes from `send`'s own length check, so there is no caller hypothesis on `p`.
`[PROVED: kernel]` -/
theorem send_inv (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c c' : Chan Q) (ps : List Frame) (p : Frame)
    (hInv : ChanInv (E := E) c ps) (h : send (E := E) c p = .ok c') : ChanInv (E := E) c' (ps ++ [p]) := by
  rung manual =>
    obtain ⟨hw, hf, hps, hcap⟩ := hInv
    unfold send at h
    split at h
    · exact absurd h (by simp)
    · rename_i hlt
      split at h
      · exact absurd h (by simp)
      · rename_i hp
        have hp : FrameOK p := Nat.lt_of_not_le hp
        simp only [Result.ok.injEq] at h
        subst h
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [hw]
        · simp [hf]
        · intro q hq
          simp only [List.mem_append, List.mem_singleton] at hq
          rcases hq with hq | rfl
          · exact hps q hq
          · exact hp
        · simp only; omega

/-- The composite: delivering the oldest pending frame pushes exactly that frame onto the
abstract queue and keeps the invariant. Proved from the laws only. `[PROVED: kernel]` -/
theorem deliver_spec (Q E : Type) [FrameCarrier E] [QueueModel Q E] [BoundedQueueLaws Q E]
    (c : Chan Q) (p : Frame) (ps : List Frame) (hInv : ChanInv (E := E) c (p :: ps)) :
    ∃ c', deliver (E := E) c = .ok c' ∧
      QueueModel.toList (Q := Q) (α := E) c'.out =
        QueueModel.toList (Q := Q) (α := E) c.out ++ [FrameCarrier.ofFrame (E := E) p] ∧ ChanInv (E := E) c' ps := by
  rung manual =>
    obtain ⟨hw, hf, hps, hcap⟩ := hInv
    have hp : FrameOK p := hps p (by simp)
    have hnf : ¬ QueueModel.full (Q := Q) (α := E) c.out := by
      apply BoundedQueueLaws.not_full_of_lt
      simp only [List.length_cons] at hf
      omega
    obtain ⟨q', hq', hlist⟩ := BoundedQueueLaws.push_law c.out (FrameCarrier.ofFrame (E := E) p) hnf
    have hparse : parseFrame c.wire = .ok (p, (ps.map encodeFrame).flatten) := by
      rw [hw]
      simp only [List.map_cons, List.flatten_cons]
      exact parseFrame_encodeFrame p _ hp
    refine ⟨{ out := q', wire := (ps.map encodeFrame).flatten, inFlight := c.inFlight - 1 },
      ?_, hlist, ?_⟩
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
    (c c' : Chan Q) (p : Frame) (hInv : ChanInv (E := E) c [])
    (h : send (E := E) c p = .ok c') :
    ∃ c'', deliver (E := E) c' = .ok c'' ∧
      QueueModel.toList (Q := Q) (α := E) c''.out =
        QueueModel.toList (Q := Q) (α := E) c.out ++ [FrameCarrier.ofFrame (E := E) p] ∧ ChanInv (E := E) c'' [] := by
  rung manual =>
    have hInv' : ChanInv (E := E) c' [p] := send_inv Q E c c' [] p hInv h
    have hout := send_out Q E c c' p h
    obtain ⟨c'', hd, hlist, hInv''⟩ := deliver_spec Q E c' p [] hInv'
    exact ⟨c'', hd, by rw [hlist, hout], hInv''⟩

/-- `send` refuses every payload that is not `FrameOK`, i.e. of `2 ^ 32` bytes or more, whatever
the capacity: the Lean statement of the Rust length guard. `[PROVED: kernel]` -/
theorem send_refuses_too_long (Q E : Type) [FrameCarrier E] [QueueModel Q E] (c : Chan Q) (p : Frame)
    (hp : ¬ FrameOK p) : send (E := E) c p = .fail := by
  rung simp => simp_all [send, FrameOK]

#print axioms decodeF_append
#print axioms toNat_lenBytes
#print axioms parseFrame_encodeFrame
#print axioms encodeFrameTable_eq
#print axioms send_out
#print axioms send_discharges_not_full
#print axioms send_bounded
#print axioms send_inv
#print axioms deliver_spec
#print axioms send_deliver
#print axioms send_refuses_too_long

end FramedChannel.Channel
