-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Varint.Defs
import FramedChannel.Model.Zigzag.Defs

/-!
# Bridge/Zigzag/Defs: the extracted signed codec, read as the model's `Int`

`[HAND-WRITTEN]` -- the definitions the zigzag refinement theorems (`Mapping.lean` and
`Instance.lean` beside this file) are stated over.

The extracted `zigzag.encode_i32` appends to an `alloc.vec.Vec Std.U8` and `zigzag.decode_i32`
reads a `Slice Std.U8`, exactly as the varint's do -- this unit delegates to `varint.encode_u32` /
`varint.decode_u32` rather than reimplementing LEB128, and so does its bridge. The byte
abstraction is therefore **reused unchanged**: `bytesOf` and `sliceOfBytes` are imported from
`Bridge/Varint/Defs.lean`, not redefined here. A second abstraction function over the same
representation would be a second thing to keep in step for no gain.

`ExtractedZigzagI32` is the component tag, and its `CodecModel` instance sits at `Std.I32` --
the interface's second value type at the bridge, as `FramedChannel.Zigzag.ZigzagI32` is at the
model's `Int`. `Dom` is the whole type: the `i32` range the model's `Dom` names explicitly is
carried by `Std.I32` itself, so nothing is left to state.

Every definition a registered zigzag bridge statement mentions is here, so
`FramedChannelAeneasChallenge.Zigzag` can import them without importing a registered theorem.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.zigzag
open framed_channel

/-- The component tag naming the extracted zigzag signed varint. -/
structure ExtractedZigzagI32 where

/-- The extracted encode, lowered: the bytes `encode_i32` appends to an empty vector. -/
noncomputable def extEncode (a : Std.I32) : List Nat :=
  match (zigzag.encode_i32 a (alloc.vec.Vec.new Std.U8)).match with
  | .ok v => varint.bytesOf v.val
  | _ => []

/-- The extracted decode, lowered: `decode_i32` on the slice holding `bs`, reporting the residual
bytes. A list no Rust slice of bytes can hold (too long, or a value of 256 or more) is refused,
exactly as the varint bridge's `extDecode` refuses it. -/
noncomputable def extDecode (bs : List Nat) : FramedChannel.Result (Std.I32 × List Nat) :=
  if h : bs.length ≤ Usize.max ∧ ∀ b ∈ bs, b < 256 then
    match (zigzag.decode_i32 (varint.sliceOfBytes bs h.1)).match with
    | .ok (.Ok (v, k)) => .ok (v, bs.drop k.val)
    | _ => .fail
  else .fail

/-- `CodecModel` on the extracted signed codec, over machine `i32` values: the domain is the whole
type, because `Std.I32` already carries the range the model's `Dom` states. -/
noncomputable instance instCodecModelExtracted : CodecModel ExtractedZigzagI32 Std.I32 where
  encode := extEncode
  decode := extDecode
  maxLen := 5
  Dom _ := True

end FramedChannel.Bridge.zigzag
