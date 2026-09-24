-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Model.Stuff.Defs

/-!
# Model/Stuff/Theorems: HDLC-style byte stuffing

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/stuff.rs` (`stuff`,
`encode_frame`, `unstuff`), over the specification layer's `Result` (`Spec/Result.lean`). Bytes are
modeled as `Nat` values below 256; the Rust `u8` range appears as the hypothesis `∀ b ∈ p, b < 256`
on the claimed domain rather than as a bounded integer type, and `stuff_bytes_lt` shows the
encoder preserves it.

## The marker-free invariant

`stuff_marker_free` is the unit's distinctive registered row and is *not* one of the two
`CodecLaws` laws. It says the stuffed payload contains no `marker` anywhere, which is exactly what
makes `unstuff`'s scan-to-flag unambiguous: the first `marker` on the wire is the frame boundary
and can be nothing else. It earns its row rather than decorating one, because without it the round
trip would not hold.

## Termination

Neither function needs fuel. `stuff` is structurally recursive on the payload. `unstuff` is
structurally recursive on the wire in its three-pattern form (see `Defs.lean`): the escape branch
recurses on `bs`, two constructors down, and the plain branch on `c :: bs`, one down. The Rust
loops are bounded by the length of the slice in hand, which is the same measure.

## Bounds

Two bounds are registered, both unconditional and input-relative: `stuff_length_le` (stuffing at
most doubles) and `encode_length_le` (one more byte for the flag). The Dom-bounded
`CodecLaws.length_le` field is discharged from `encode_length_le` together with the domain's
`p.length ≤ 255`; `Evidence/Countermodels.lean` refutes the same bound without that hypothesis.
-/

namespace FramedChannel.Stuff

/-! ## The escape constants agree with the RFC 1662 xor -/

/-- The escaped marker is the marker xor the transparency mask, as RFC 1662 asynchronous framing
specifies and as `rust/src/stuff.rs`'s `b ^ XOR_MASK` computes. `[PROVED: kernel]` -/
theorem escMarker_eq : escMarker = marker ^^^ xorMask := by decide

/-- The escaped escape byte is the escape byte xor the transparency mask. `[PROVED: kernel]` -/
theorem escEsc_eq : escEsc = esc ^^^ xorMask := by decide

/-- `[PROVED: kernel]` -/
theorem esc_ne_marker : esc ≠ marker := by decide

/-- `[PROVED: kernel]` -/
theorem escMarker_ne_marker : escMarker ≠ marker := by decide

/-- `[PROVED: kernel]` -/
theorem escEsc_ne_marker : escEsc ≠ marker := by decide

/-! ## The per-byte equations -/

/-- `[PROVED: kernel]` -/
theorem stuffByte_marker : stuffByte marker = [esc, escMarker] := by simp [stuffByte]

/-- `[PROVED: kernel]` -/
theorem stuffByte_esc : stuffByte esc = [esc, escEsc] := by simp [stuffByte, esc_ne_marker]

/-- `[PROVED: kernel]` -/
theorem stuffByte_other (b : Nat) (h1 : b ≠ marker) (h2 : b ≠ esc) : stuffByte b = [b] := by
  simp [stuffByte, h1, h2]

/-- No byte of a stuffed byte is the marker: the escape sequences start with `esc` and carry the
xor-masked value, and an unreserved byte is not the marker by hypothesis. `[PROVED: kernel]` -/
theorem stuffByte_marker_free (b : Nat) : ∀ c ∈ stuffByte b, c ≠ marker := by
  intro c hc
  unfold stuffByte at hc
  split at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact esc_ne_marker
    · exact escMarker_ne_marker
  · rename_i h1
    split at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact esc_ne_marker
      · exact escEsc_ne_marker
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; exact h1

/-! ## The marker-free invariant -/

/-- The marker-free encoding invariant: a stuffed payload contains no frame boundary byte. This is
what makes `unstuff`'s scan-to-flag unambiguous and what the round trip below rests on.
`[PROVED: kernel]` -/
theorem stuff_marker_free (p : List Nat) : ∀ c ∈ stuff p, c ≠ marker := by
  rung manual =>
    induction p with
    | nil => simp [stuff]
    | cons b bs ih =>
        intro c hc
        simp only [stuff, List.mem_append] at hc
        rcases hc with h | h
        · exact stuffByte_marker_free b c h
        · exact ih c h

/-! ## The round trip -/

/-- A non-reserved byte at the head of a non-empty wire is payload: the decoder pushes it and
carries on. Stated separately because the plain branch of `unstuff` recurses on `c :: bs`, so the
equation only applies once the tail is known to be non-empty. `[PROVED: kernel]` -/
theorem unstuff_cons_plain (b : Nat) (h1 : b ≠ marker) (h2 : b ≠ esc) (acc w : List Nat)
    (hw : w ≠ []) : unstuff acc (b :: w) = unstuff (b :: acc) w := by
  cases w with
  | nil => exact absurd rfl hw
  | cons x xs => rw [unstuff]; simp only [if_neg h1, if_neg h2]

/-- A stuffed payload followed by the flag is never the empty wire, which is what discharges
`unstuff_cons_plain`'s side condition in the inductive step. `[PROVED: kernel]` -/
theorem stuff_append_marker_ne_nil (p rest : List Nat) : stuff p ++ marker :: rest ≠ [] := by
  cases p <;> simp [stuff, stuffByte] <;> split <;> simp

/-- The decoder's loop invariant, generalized over the accumulator and the residual: reading a
stuffed payload followed by the flag returns the accumulator's reverse extended by the payload,
and leaves the residual untouched. The three cases of the inductive step are the three branches of
`stuffByte`. `[PROVED: kernel]` -/
theorem unstuff_stuff (p : List Nat) : ∀ acc rest : List Nat,
    unstuff acc (stuff p ++ marker :: rest) = .ok (acc.reverse ++ p, rest) := by
  induction p with
  | nil =>
      intro acc rest
      simp only [stuff, List.nil_append]
      cases rest with
      | nil => rw [unstuff.eq_2]; simp
      | cons x xs => rw [unstuff.eq_3]; simp
  | cons b bs ih =>
      intro acc rest
      rw [show stuff (b :: bs) = stuffByte b ++ stuff bs from rfl]
      by_cases h1 : b = marker
      · subst h1
        rw [stuffByte_marker]
        simp only [List.cons_append, List.nil_append]
        rw [unstuff.eq_3]
        simp only [if_neg esc_ne_marker, ih]
        simp
      · by_cases h2 : b = esc
        · subst h2
          rw [stuffByte_esc]
          simp only [List.cons_append, List.nil_append]
          rw [unstuff.eq_3]
          simp only [if_neg esc_ne_marker, if_neg (show escEsc ≠ escMarker by decide), ih]
          simp
        · rw [stuffByte_other b h1 h2]
          simp only [List.cons_append, List.nil_append]
          rw [unstuff_cons_plain b h1 h2 acc _ (stuff_append_marker_ne_nil bs rest), ih]
          simp

/-- The round-trip law (the `D ∘ E = id` row): every payload decodes to itself with nothing left
over. Unlike `Varint.varint_roundtrip` this needs no domain hypothesis -- stuffing round-trips at
every payload, bounded or not. `[PROVED: kernel]` -/
theorem stuff_roundtrip (p : List Nat) : decode (encode p) = .ok (p, []) := by
  rung retrieval => simpa [decode, encode] using unstuff_stuff p [] []

/-! ## Bounds: stuffing at most doubles -/

/-- Bounds: stuffing at most doubles the payload, since the worst case emits two bytes per input
byte. This is the unit's real bounds row: it is unconditional and input-relative, so it is
strictly more informative than the constant `CodecLaws.length_le` demands.
`[PROVED: kernel]` -/
theorem stuff_length_le (p : List Nat) : (stuff p).length ≤ 2 * p.length := by
  rung manual =>
    induction p with
    | nil => simp [stuff]
    | cons b bs ih =>
        simp only [stuff, stuffByte, List.length_append, List.length_cons]
        split
        · simp; omega
        · split <;> simp <;> omega

/-- Bounds on the whole frame: the stuffed payload plus the one terminating flag byte. This is
what discharges `CodecLaws.length_le` on the claimed domain; without the domain's
`p.length ≤ 255`, the constant bound `maxLen` asks for is false, and
`Evidence/Countermodels.lean` refutes it in the kernel. `[PROVED: kernel]` -/
theorem encode_length_le (p : List Nat) : (encode p).length ≤ 2 * p.length + 1 := by
  rung manual =>
    simp only [encode, List.length_append, List.length_cons, List.length_nil]
    have := stuff_length_le p
    omega

/-! ## Byte-range preservation -/

/-- The encoder stays inside the byte range: the escape sequences emit `esc`, `escMarker` and
`escEsc`, all below 256, and a copied-through byte was in range by hypothesis. The counterpart of
`Varint.encodeF_bytes_lt`, and the reason the `Dom`'s byte-range condition is preserved by
encoding. `[PROVED: kernel]` -/
theorem stuff_bytes_lt (p : List Nat) (h : ∀ b ∈ p, b < 256) : ∀ c ∈ stuff p, c < 256 := by
  induction p with
  | nil => simp [stuff]
  | cons b bs ih =>
      intro c hc
      simp only [stuff, List.mem_append] at hc
      rcases hc with hc | hc
      · unfold stuffByte at hc
        split at hc
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> decide
        · split at hc
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl <;> decide
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            subst hc; exact h c (by simp)
      · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) c hc

/-! ## The interface instance

`CodecModel` (L0) and `CodecLaws` (L1) are specification, declared in `Spec/Codec.lean`. `Hdlc` is
the component tag the stateless codec is indexed by. -/

/-- The refinement certificate as an interface instance: the HDLC stuffing codec satisfies the
codec laws. `round_trip` discharges from `stuff_roundtrip`, which needs no hypothesis at all;
`length_le` from `encode_length_le` together with the domain's payload-length bound.
`[PROVED: kernel]` -/
instance instCodecLaws : CodecLaws Hdlc (List Nat) where
  round_trip := fun p _ => stuff_roundtrip p
  length_le := fun p hp => by
    have := encode_length_le p
    have h2 : p.length ≤ 255 := hp.2
    simp only [CodecModel.encode, CodecModel.maxLen] at *
    omega

ladder_record% instCodecLaws instance

#print axioms escMarker_eq
#print axioms escEsc_eq
#print axioms stuffByte_marker_free
#print axioms stuff_marker_free
#print axioms unstuff_stuff
#print axioms stuff_roundtrip
#print axioms stuff_length_le
#print axioms encode_length_le
#print axioms stuff_bytes_lt
#print axioms instCodecLaws

end FramedChannel.Stuff
