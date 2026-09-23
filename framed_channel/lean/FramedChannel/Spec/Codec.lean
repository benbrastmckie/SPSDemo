-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Result

/-!
# Spec/Codec: the codec interface, `CodecModel` (L0) and `CodecLaws` (L1)

The same two-layer anatomy `Spec/Queue.lean` gives the queue, at the codec: `CodecModel` carries
operations and types only, and `CodecLaws` states the laws over the observation a decode produces
-- the decoded value together with the residual bytes.

A codec is stateless, so the representation parameter `C` degenerates to a tag naming the codec as
a library component, where `QueueModel`'s `Q` is a real state type. The interface still has a
carrier, and `Model/Varint/Theorems.lean`'s `Leb128` is an inhabited instance of it, so neither class is
vacuous.
-/

namespace FramedChannel

/-- L0: the operations of a byte-list codec for values of type `α`, indexed by a component tag
`C`. Operations and types only. -/
class CodecModel (C : Type) (α : Type) where
  /-- Encode a value as a byte list (bytes are `Nat` below 256; see `Varint.encodeF_bytes_lt`). -/
  encode : α → List Nat
  /-- Decode one value off the front of a byte list, returning it with the residual bytes. -/
  decode : List Nat → Result (α × List Nat)
  /-- The length bound the encoding claims on `Dom`. -/
  maxLen : Nat
  /-- The domain the codec claims. Values outside it are not covered by `CodecLaws`. -/
  Dom : α → Prop

/-- L1: the laws a codec must satisfy, stated through the decode observation. -/
class CodecLaws (C : Type) (α : Type) [CodecModel C α] : Prop where
  /-- Round trip (the `D ∘ E = id` row): on the claimed domain, decoding an encoding
  returns the value with nothing left over. -/
  round_trip : ∀ a : α, CodecModel.Dom (C := C) a →
    CodecModel.decode (C := C) (CodecModel.encode (C := C) a) = .ok (a, [])
  /-- Length bound: on the claimed domain, the encoding fits in `maxLen` bytes. -/
  length_le : ∀ a : α, CodecModel.Dom (C := C) a →
    (CodecModel.encode (C := C) a).length ≤ CodecModel.maxLen (C := C) (α := α)

end FramedChannel
