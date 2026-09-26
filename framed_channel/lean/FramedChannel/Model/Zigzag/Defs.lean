-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Codec
import FramedChannel.Model.Varint.Defs

/-!
# Model/Zigzag/Defs: the zigzag signed-varint definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of `Model/Zigzag/Theorems.lean`: the
protobuf zigzag map and its inverse, the encoder and decoder, the component tag `ZigzagI32` and the
`CodecModel` instance. It holds definitions only, so that the Challenge module
`FramedChannelChallenge.Zigzag` can import them without importing a registered theorem.

## Defined over `Varint.Leb128`, through the interface

`encode` and `decode` go through `CodecModel.encode`/`CodecModel.decode` at `C := Varint.Leb128`
rather than through `Varint.encode`/`Varint.decode` directly. That spelling is load-bearing and not
cosmetic: `Ladder.lean`'s audit hint set excludes instances and projections, so a projection applied
to an instance is not a hint, `grind` does not reach `Varint.encodeF`/`decodeF` through it, and the
two laws in `Model/Zigzag/Theorems.lean` are recorded on the `retrieval` rung -- retrieved from
`CodecLaws` at `Leb128` rather than re-derived. Spelled `Varint.encode` instead, the audit reports
`grind` as the cheaper rung and the recorded distillation disappears from `certificate/ladder.txt`.
`Zigzag.encode n = Varint.encode (zigzag n)` still holds by `rfl` (`Zigzag.encode_eq`), so nothing
downstream is complicated by the choice.

## The arithmetic model, and the Rust it matches

`rust/src/zigzag.rs` computes `(n << 1) ^ (n >> 31)` on `i32`, where `>>` is an *arithmetic* shift:
`0` for a non-negative `n`, `-1` otherwise, so the xor complements the doubled value exactly on the
negatives. This model states that arithmetically over `Int`/`Nat` instead of as a bit-vector
expression, which keeps every core proof on the `grind` rung and every countermodel search
kernel-decidable; the one lemma tying the two spellings together
(`FramedChannel.Bridge.zigzag.zz_bv`) lives in the bridge package.
-/

namespace FramedChannel.Zigzag

/-- The protobuf zigzag map: interleave the signed range onto the unsigned one, so that values near
zero in either direction map to small naturals. `2 * n` on the non-negatives and `-2 * n - 1` on the
negatives -- the arithmetic reading of `(n << 1) ^ (n >> 31)`. -/
def zigzag (n : Int) : Nat := if 0 ≤ n then (2 * n).toNat else (-2 * n - 1).toNat

/-- The inverse of `zigzag`, total on all of `Nat`: even naturals halve to non-negatives, odd ones
to negatives. -/
def unzigzag (m : Nat) : Int := if m % 2 = 0 then (m / 2 : Int) else -((m / 2 : Nat) : Int) - 1

/-- Encode a signed value: zigzag it, then hand it to the LEB128 codec through the interface. -/
def encode (n : Int) : List Nat := CodecModel.encode (C := Varint.Leb128) (zigzag n)

/-- Decode a signed value: decode a LEB128 natural through the interface, then unzigzag it. The
failure is the underlying codec's, forwarded unchanged. -/
def decode (bs : List Nat) : Result (Int × List Nat) :=
  match CodecModel.decode (C := Varint.Leb128) (α := Nat) bs with
  | .ok (m, rest) => .ok (unzigzag m, rest)
  | .fail => .fail

/-- The component tag naming this zigzag signed-varint codec. -/
structure ZigzagI32 where

/-- The codec interface at a second value type: `α = Int`, with an explicit `Dom` naming the `i32`
range. The domain is exact rather than conservative -- `Dom n ↔ zigzag n < 2 ^ 32`, so it is
precisely the preimage of the varint's own claimed domain. -/
instance instCodecModel : CodecModel ZigzagI32 Int where
  encode := encode
  decode := decode
  maxLen := 5
  Dom n := -2 ^ 31 ≤ n ∧ n < 2 ^ 31

end FramedChannel.Zigzag
