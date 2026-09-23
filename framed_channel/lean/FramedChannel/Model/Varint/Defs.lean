-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Result
import FramedChannel.Spec.Codec

/-!
# Model/Varint/Defs: the LEB128 encoder and decoder definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of `Model/Varint/Theorems.lean`: the fuel-indexed
encoder and decoder, their fuel-5 wrappers, the component tag `Leb128` and the `CodecModel`
instance. It holds definitions only, so that the Challenge module `FramedChannelChallenge.Varint`
can import them without importing a registered theorem.
-/

namespace FramedChannel.Varint

/-- `encode_u32`, fuel-indexed: emit seven bits with the continuation bit set while the value
does not fit in seven bits. -/
def encodeF : Nat → Nat → List Nat
  | 0, n => [n % 128]
  | fuel + 1, n => if n < 128 then [n] else (n % 128 + 128) :: encodeF fuel (n / 128)

/-- `decode_u32`, fuel-indexed. `m` is the multiplier of the next group (`1, 128, 128^2, ...`),
`acc` the value assembled so far. Returns the value and the unconsumed bytes. -/
def decodeF : Nat → Nat → Nat → List Nat → Result (Nat × List Nat)
  | 0, _, _, _ => .fail
  | _ + 1, _, _, [] => .fail
  | fuel + 1, m, acc, b :: bs =>
      if b < 128 then .ok (acc + b * m, bs)
      else decodeF fuel (m * 128) (acc + (b - 128) * m) bs

def encode (n : Nat) : List Nat := encodeF 5 n

def decode (bs : List Nat) : Result (Nat × List Nat) := decodeF 5 1 0 bs

/-- The component tag naming this LEB128 codec. -/
structure Leb128 where

/-- The canonical model of `CodecModel`: LEB128 over `u32`-ranged naturals. -/
instance instCodecModel : CodecModel Leb128 Nat where
  encode := encode
  decode := decode
  maxLen := 5
  Dom n := n < 2 ^ 32

end FramedChannel.Varint
