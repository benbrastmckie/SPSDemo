-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs
import FramedChannel.Model.RingBuffer.Defs
import FramedChannelAeneas.Bridge.Queue.Defs

/-!
# Bridge/RingBuffer/Defs: the extracted ring buffer, read as the hand-written model

`[HAND-WRITTEN]` -- the abstraction function the ring buffer's refinement theorems
(`Refinement.lean` beside this file) are stated over.

`Extracted/Funs.lean` is what Charon and Aeneas produce from `rust/src/ring_buffer.rs`: a
`ring_buffer.RingBuffer T` with `buf : alloc.vec.Vec T` and `head tail len : Std.Usize`, and
functions in Aeneas's `Result` monad that take the `Default` and `Clone` trait records explicitly
(see `Bridge/Queue/Traits.lean`). `toModel` forgets the machine representation -- `Vec` to its `List`,
each `Usize` to its `Nat` value -- and lands in `FramedChannel.RingBuffer`
(`lean/FramedChannel/Model/RingBuffer/Theorems.lean`), the model the `BQ` interface instance is built on.

It also defines the extracted carrier `ExtractedRB`. Every definition a registered ring buffer
bridge statement mentions is here, so the Challenge module can import them without importing a
registered theorem.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.ring_buffer
open framed_channel

variable {α : Type}

/-- The abstraction function: each machine field to its mathematical value. -/
def toModel (r : ring_buffer.RingBuffer α) : FramedChannel.RingBuffer α :=
  { buf := r.buf.val, head := r.head.val, tail := r.tail.val, len := r.len.val }

/-- The extracted carrier of the ring buffer: extracted buffers related to a `BQ` value. -/
abbrev ExtractedRB (α : Type) [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) : Type :=
  Ext (ring_buffer.RingBuffer α) (FramedChannel.RingBuffer.BQ α) α
    (ring_buffer.RingBuffer.Insts.Framed_channelQueueBoundedQueue dflt cln)
    (fun s q => toModel s = q.1)

end FramedChannel.Bridge.ring_buffer
