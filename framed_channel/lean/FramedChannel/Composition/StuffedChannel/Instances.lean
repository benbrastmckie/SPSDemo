-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Composition.StuffedChannel.Theorems
import FramedChannel.Model.Stuff.Theorems
import FramedChannel.Model.Crc8.Theorems
import FramedChannel.Model.RingBuffer.Theorems
import FramedChannel.Model.VecQueue.Theorems

/-!
# Composition/StuffedChannel/Instances: where the three interfaces meet their models

`Composition/StuffedChannel/Theorems.lean` proves every theorem from `Spec/Queue.lean`,
`Spec/Codec.lean`'s L0 plus the composition-layer `Transparent` bundle, and `Spec/Checksum.lean`'s
L0 -- and imports no queue model, no `Model/Stuff/Theorems` and no `Model/Crc8/Theorems`. This
module is where the composition layer meets the model layer, three times over:

* `instTransparentHdlc` discharges the `Transparent` bundle at HDLC byte stuffing, from
  `Stuff.unstuff_stuff` and `Stuff.stuff_marker_free`. Those two are already in the model layer:
  nothing new about stuffing is proved here, which is what makes the composite's claim a
  composition rather than a restatement;
* `deliver_spec_RB` and `deliver_spec_VQ` instantiate the one `deliver_spec` proof at the ring
  buffer (`RingBuffer.BQ`) and at the list-backed queue (`VecQueue.VQ`) with no reproof. That is
  the substitution row `StuffedChannel[VQ/BQ]`, the same row `Channel` exercises, now exercised at
  a second composite;
* both instantiations fix the checksum at `Crc8.Bitwise`, the digest the Rust `crc8` computes.

The declarations are in namespace `FramedChannel.StuffedChannel`, beside the theorems they
instantiate.
-/

namespace FramedChannel.StuffedChannel

open FramedChannel
open FramedChannel.Channel (Frame)

/-- The composition-layer transparency bundle, discharged at HDLC stuffing. `decode_append` is
`Stuff.unstuff_stuff`'s loop invariant at the empty accumulator; `body_flag_free` is
`Stuff.stuff_marker_free` after dropping the terminating flag; `ends_with_flag` is the shape of
`Stuff.encode` itself. -/
instance instTransparentHdlc : Transparent Stuff.Hdlc Stuff.marker where
  decode_append p rest := by
    show Stuff.decode (Stuff.encode p ++ rest) = .ok (p, rest)
    simp only [Stuff.encode, Stuff.decode, List.append_assoc, List.cons_append, List.nil_append]
    simpa using Stuff.unstuff_stuff p [] rest
  body_flag_free p c hc := by
    show c ≠ Stuff.marker
    have hdl : (CodecModel.encode (C := Stuff.Hdlc) p).dropLast = Stuff.stuff p := by
      simp [CodecModel.encode, Stuff.encode]
    rw [hdl] at hc
    exact Stuff.stuff_marker_free p c hc
  ends_with_flag p := by simp [CodecModel.encode, Stuff.encode]

ladder_record% instTransparentHdlc instance

/-- `deliver_spec` at the ring buffer, HDLC framing, bitwise CRC-8. `[PROVED: kernel]` -/
theorem deliver_spec_RB (c : SChan (RingBuffer.BQ Frame)) (p : Frame) (ps : List Frame)
    (h : SChanInv (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c (p :: ps)) :
    ∃ c', deliver (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c = .ok c' ∧
      c'.out.1.contents = c.out.1.contents ++ [p] ∧
      SChanInv (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c' ps := by
  rung retrieval =>
    exact deliver_spec (C := Stuff.Hdlc) (K := Crc8.Bitwise) (RingBuffer.BQ Frame) Frame
      Stuff.marker c p ps h

/-- The same proof at the list-backed queue, with no reproof. `[PROVED: kernel]` -/
theorem deliver_spec_VQ (c : SChan (VecQueue.VQ Frame)) (p : Frame) (ps : List Frame)
    (h : SChanInv (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c (p :: ps)) :
    ∃ c', deliver (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c = .ok c' ∧
      c'.out.items = c.out.items ++ [p] ∧
      SChanInv (C := Stuff.Hdlc) (K := Crc8.Bitwise) (E := Frame) c' ps := by
  rung retrieval =>
    exact deliver_spec (C := Stuff.Hdlc) (K := Crc8.Bitwise) (VecQueue.VQ Frame) Frame
      Stuff.marker c p ps h

#print axioms instTransparentHdlc
#print axioms deliver_spec_RB
#print axioms deliver_spec_VQ

end FramedChannel.StuffedChannel
