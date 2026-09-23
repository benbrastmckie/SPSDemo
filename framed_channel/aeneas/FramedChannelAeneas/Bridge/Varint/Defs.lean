-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs
import FramedChannel.Model.Varint.Defs

/-!
# Bridge/Varint/Defs: extracted bytes, read as the model's byte list

`[HAND-WRITTEN]` -- the abstraction function the varint refinement theorems (`Encode.lean`,
`Decode.lean` and `Instance.lean` beside this file) are stated over.

The extracted `varint.encode_u32` appends to an `alloc.vec.Vec Std.U8`, and `varint.decode_u32`
reads a `Slice Std.U8`. The hand-written model `FramedChannel.Varint`
(`lean/FramedChannel/Model/Varint/Theorems.lean`) works over `List Nat`, bytes as naturals below 256.
`bytesOf` maps each machine byte to its value; the bound below 256 is then carried by `Std.U8`
itself rather than stated.

It also defines the extracted codec's `CodecModel` instance and what it is built from:
`ExtractedLeb128`, `sliceOfBytes`, `extEncode` and `extDecode`. Every definition a registered varint
bridge statement mentions is here, so the Challenge module can import them without importing a
registered theorem.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.varint

/-- The abstraction function: each machine byte to its natural-number value. -/
def bytesOf (v : List Std.U8) : List Nat := v.map (·.val)

end FramedChannel.Bridge.varint

namespace FramedChannel.Bridge.varint
open framed_channel

/-- The component tag naming the extracted LEB128 codec. -/
structure ExtractedLeb128 where

/-- A byte list as a machine slice (each value reduced modulo 256; the decode below only calls
this on lists that are already bytes, where the reduction is the identity). -/
def sliceOfBytes (bs : List Nat) (h : bs.length ≤ Usize.max) : Slice Std.U8 :=
  Slice.from (bs.map fun b => UScalar.ofNatCore (b % 256) (by
    have := Nat.mod_lt b (show 256 > 0 by decide)
    simpa using this)) (by simpa using h)

/-- The extracted encode, lowered: the bytes `encode_u32` appends to an empty vector. -/
noncomputable def extEncode (a : Std.U32) : List Nat :=
  match (varint.encode_u32 a (alloc.vec.Vec.new Std.U8)).match with
  | .ok v => bytesOf v.val
  | _ => []

/-- The extracted decode, lowered: `decode_u32` on the slice holding `bs`, reporting the residual
bytes. A list no Rust slice of bytes can hold (too long, or a value of 256 or more) is refused. -/
noncomputable def extDecode (bs : List Nat) : FramedChannel.Result (Std.U32 × List Nat) :=
  if h : bs.length ≤ Usize.max ∧ ∀ b ∈ bs, b < 256 then
    match (varint.decode_u32 (sliceOfBytes bs h.1)).match with
    | .ok (.Ok (v, k)) => .ok (v, bs.drop k.val)
    | _ => .fail
  else .fail

/-- `CodecModel` on the extracted codec, over machine `u32` values: the domain is the whole type. -/
noncomputable instance instCodecModelExtracted : CodecModel ExtractedLeb128 Std.U32 where
  encode := extEncode
  decode := extDecode
  maxLen := 5
  Dom _ := True

end FramedChannel.Bridge.varint
