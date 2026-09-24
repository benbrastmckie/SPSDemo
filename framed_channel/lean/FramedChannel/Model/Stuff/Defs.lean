-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Result
import FramedChannel.Spec.Codec

/-!
# Model/Stuff/Defs: the HDLC byte-stuffing encoder and decoder definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of `Model/Stuff/Theorems.lean`: the five
wire constants, the per-byte stuffing function, the whole-payload encoder, the structurally
recursive decoder, the component tag `Hdlc` and the `CodecModel` instance. It holds definitions
only, so that the Challenge module `FramedChannelChallenge.Stuff` can import them without
importing a registered theorem.

## The escape constants

RFC 1662 asynchronous framing sends an escaped byte as `esc` followed by the byte xor `xorMask`,
so `marker` travels as `esc, escMarker` and `esc` as `esc, escEsc`. The two escaped values are
written here as literal constants rather than as `marker ^^^ xorMask` inside `stuffByte`: the
literals keep the equation lemmas of `stuffByte` and `unstuff` on cheap proof rungs, and
`Theorems.lean`'s `escMarker_eq`/`escEsc_eq` check the xor identities in the kernel, so no
fidelity to the standard -- or to `rust/src/stuff.rs`'s `b ^ XOR_MASK` -- is given up.

## Why `unstuff` has three patterns

`unstuff` matches `[]`, `[b]` and `b :: c :: bs` rather than matching `[]` and `b :: rest` and
then matching `rest` again inside the cons branch. The two formulations are equal, but only the
three-pattern one produces the unconditional equation lemmas `unstuff.eq_1/eq_2/eq_3` that
`Theorems.lean`'s round-trip proof rewrites with; the nested form's equations are guarded by the
inner match and do not fire. The shape is load-bearing, not stylistic.
-/

namespace FramedChannel.Stuff

/-- The frame boundary byte, the HDLC flag (`stuff::MARKER`). -/
def marker : Nat := 0x7E

/-- The escape byte (`stuff::ESC`). -/
def esc : Nat := 0x7D

/-- The transparency mask (`stuff::XOR_MASK`). -/
def xorMask : Nat := 0x20

/-- The escaped form of `marker`: `marker ^^^ xorMask` (see `escMarker_eq`). -/
def escMarker : Nat := 0x5E

/-- The escaped form of `esc`: `esc ^^^ xorMask` (see `escEsc_eq`). -/
def escEsc : Nat := 0x5D

/-- One byte's stuffed form (`stuff::stuff`'s loop body): the two reserved bytes become a
two-byte escape sequence, every other byte is copied through. -/
def stuffByte (b : Nat) : List Nat :=
  if b = marker then [esc, escMarker]
  else if b = esc then [esc, escEsc]
  else [b]

/-- The byte-stuffed form of a payload (`stuff::stuff`): stuff each byte and concatenate. The
result contains no `marker` (`stuff_marker_free`). -/
def stuff : List Nat → List Nat
  | [] => []
  | b :: bs => stuffByte b ++ stuff bs

/-- One framed message on the wire (`stuff::encode_frame`): the stuffed payload followed by the
terminating flag. The trailing flag is what makes the codec self-delimiting, which is what lets
`decode` return the residual bytes `CodecModel.decode`'s shape asks for. -/
def encode (p : List Nat) : List Nat := stuff p ++ [marker]

/-- The decoder's accumulating loop (`stuff::unstuff`): `acc` holds the payload bytes read so far,
in reverse. A bare `marker` ends the frame and the rest of the wire is the residual; an `esc`
consumes the following byte and unescapes it; anything else is payload. The wire running out
before a `marker`, and an `esc` followed by neither escaped value, both refuse. -/
def unstuff : List Nat → List Nat → Result (List Nat × List Nat)
  | _, [] => .fail
  | acc, [b] => if b = marker then .ok (acc.reverse, []) else .fail
  | acc, b :: c :: bs =>
      if b = marker then .ok (acc.reverse, c :: bs)
      else if b = esc then
        (if c = escMarker then unstuff (marker :: acc) bs
         else if c = escEsc then unstuff (esc :: acc) bs
         else .fail)
      else unstuff (b :: acc) (c :: bs)

/-- Read one framed message off the front of the wire. -/
def decode (bs : List Nat) : Result (List Nat × List Nat) := unstuff [] bs

/-- The component tag naming this HDLC-style stuffing codec. -/
structure Hdlc where

/-- The canonical model of `CodecModel`: byte stuffing over payloads of bytes.

`Dom` carries a length bound as well as the byte-range condition, and this is the unit's one
genuinely discretionary modelling choice. `CodecLaws.length_le` bounds an encoding by the
*constant* `maxLen`, while stuffing expands with the input, so the unconditional form is false --
`Evidence/Countermodels.lean` refutes it. `maxPayload = 255` keeps a stuffed frame under 512
bytes on the wire and keeps that refutation decidable in the kernel; the rationale is recorded in
`certificate/stuff.yaml`. The unconditional, input-relative bounds live in `stuff_length_le` and
`encode_length_le`, which are strictly more informative than any constant. -/
instance instCodecModel : CodecModel Hdlc (List Nat) where
  encode := encode
  decode := decode
  maxLen := 2 * 255 + 1
  Dom p := (∀ b ∈ p, b < 256) ∧ p.length ≤ 255

end FramedChannel.Stuff
