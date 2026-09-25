-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs
import FramedChannel.Model.Stuff.Defs

/-!
# Bridge/Stuff/Defs: extracted bytes, read as the model's byte list

`[HAND-WRITTEN]` -- the abstraction function the byte-stuffing refinement theorems (`Stuff.lean`,
`Unstuff.lean` and `Instance.lean` beside this file) are stated over.

The extracted `stuff.stuff` and `stuff.encode_frame` append to an `alloc.vec.Vec Std.U8`, and
`stuff.unstuff` reads a `Slice Std.U8` and returns a fresh vector together with the number of bytes
it consumed. The hand-written model `FramedChannel.Stuff`
(`lean/FramedChannel/Model/Stuff/Theorems.lean`) works over `List Nat`, bytes as naturals below
256. `bytesOf` maps each machine byte to its value; the bound below 256 is then carried by
`Std.U8` itself rather than stated.

It also defines the extracted codec's `CodecModel` instance and what it is built from:
`ExtractedHdlc`, `sliceOfBytes`, `extEncode` and `extDecode`. Every definition a registered
byte-stuffing bridge statement mentions is here, so the Challenge module can import them without
importing a registered theorem.

Unlike the varint codec, whose values are machine `u32`s, a stuffing payload has no machine
counterpart smaller than the byte list itself, so the extracted instance is stated over `List Nat`
exactly as the model's is, and `Dom` repeats the model's domain. A byte list no Rust slice can hold
(longer than `usize::MAX`, or carrying a value of 256 or more) is refused by both operations.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuff

/-- The abstraction function: each machine byte to its natural-number value. -/
def bytesOf (v : List Std.U8) : List Nat := v.map (·.val)

end FramedChannel.Bridge.stuff

namespace FramedChannel.Bridge.stuff
open framed_channel

/-- The component tag naming the extracted HDLC-style stuffing codec. -/
structure ExtractedHdlc where

/-- A byte list as a machine slice (each value reduced modulo 256; the operations below only call
this on lists that are already bytes, where the reduction is the identity). -/
def sliceOfBytes (bs : List Nat) (h : bs.length ≤ Usize.max) : Slice Std.U8 :=
  Slice.from (bs.map fun b => UScalar.ofNatCore (b % 256) (by
    have := Nat.mod_lt b (show 256 > 0 by decide)
    simpa using this)) (by simpa using h)

/-- The extracted framing encode, lowered: the bytes `encode_frame` appends to an empty vector. -/
noncomputable def extEncode (p : List Nat) : List Nat :=
  if h : p.length ≤ Usize.max ∧ ∀ b ∈ p, b < 256 then
    match (stuff.encode_frame (sliceOfBytes p h.1) (alloc.vec.Vec.new Std.U8)).match with
    | .ok v => bytesOf v.val
    | _ => []
  else []

/-- The extracted decode, lowered: `unstuff` on the slice holding `bs`, reporting the unstuffed
payload and the residual bytes after the terminating flag. -/
noncomputable def extDecode (bs : List Nat) : FramedChannel.Result (List Nat × List Nat) :=
  if h : bs.length ≤ Usize.max ∧ ∀ b ∈ bs, b < 256 then
    match (stuff.unstuff (sliceOfBytes bs h.1)).match with
    | .ok (.Ok (v, k)) => .ok (bytesOf v.val, bs.drop k.val)
    | _ => .fail
  else .fail

/-- `CodecModel` on the extracted codec, over byte lists, with the model's own domain. -/
noncomputable instance instCodecModelExtracted : CodecModel ExtractedHdlc (List Nat) where
  encode := extEncode
  decode := extDecode
  maxLen := 2 * 255 + 1
  Dom p := (∀ b ∈ p, b < 256) ∧ p.length ≤ 255

end FramedChannel.Bridge.stuff
