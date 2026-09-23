-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs
import FramedChannel.Model.VecQueue.Defs
import FramedChannelAeneas.Bridge.Queue.Defs

/-!
# Bridge/VecQueue/Defs: the extracted list-backed queue, read as the hand-written model

`[HAND-WRITTEN]` -- the abstraction function the list-backed queue's refinement theorems
(`Refinement.lean` beside this file) are stated over.

`Extracted/Funs.lean` is what Charon and Aeneas produce from `rust/src/queue.rs`'s `VecQueue<T>`:
a `queue.VecQueue T` with `items : alloc.vec.Vec T` and `cap : Std.Usize`, and functions in
Aeneas's `Result` monad that take only a `Clone` trait record (no `Default`). `toModel` forgets
the machine representation -- `Vec` to its `List`, `Usize` to its `Nat` value -- and lands in
`FramedChannel.VecQueue.VQ` (`lean/FramedChannel/Model/VecQueue/Theorems.lean`). It is total: `VQ`
carries no invariant, so every extracted state has a model.

It also defines the extracted carrier `ExtractedVQ`. Every definition a registered `VecQueue`
bridge statement mentions is here, so the Challenge module can import them without importing a
registered theorem.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.vec_queue
open framed_channel

variable {α : Type}

/-- The abstraction function: the backing vector to its list, the bound to its value. -/
def toModel (s : queue.VecQueue α) : FramedChannel.VecQueue.VQ α :=
  { items := s.items.val, cap := s.cap.val }

/-- The extracted carrier of the list-backed queue. -/
abbrev ExtractedVQ (α : Type) (cln : core.clone.Clone α) : Type :=
  Ext (queue.VecQueue α) (FramedChannel.VecQueue.VQ α) α
    (queue.VecQueue.Insts.Framed_channelQueueBoundedQueue cln)
    (fun s q => toModel s = q)

end FramedChannel.Bridge.vec_queue
