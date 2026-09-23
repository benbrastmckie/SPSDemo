-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Transport
import FramedChannelAeneas.Bridge.VecQueue.Defs
import FramedChannel.Model.VecQueue.Theorems

/-!
# Bridge/VecQueue/Refinement: the extracted list-backed queue refines the hand-written model

`[EXTRACTED: aeneas + bridge]` -- kernel-checked theorems connecting the Charon/Aeneas
extraction of `rust/src/queue.rs`'s `VecQueue<T>` (`Extracted/Funs.lean`, generated, never
hand-edited) to `FramedChannel.VecQueue.VQ` (`lean/FramedChannel/Model/VecQueue/Theorems.lean`,
hand-written), through `toModel` (`Defs.lean` beside this file).

* `push_full`, `pop_empty`: at the bound (on an empty queue) the extracted `push` (`pop`) returns
  `Err(Full)` (`None`) and leaves the queue unchanged -- the model's `.fail` branch.
* `push_refines`, `pop_refines`: otherwise the extracted operation succeeds and its result
  abstracts to exactly what the model's `push`/`pop` returns. Neither needs a hypothesis beyond
  the branch condition: the `Vec::push` overflow obligation `items.len < Usize.max` follows from
  `items.len < cap ≤ Usize.max`, carried by the machine integer `cap`, and `pop`'s
  `Vec::remove(0)` is in range because the queue is non-empty.
* `capacity_agrees`, `len_agrees`, `is_full_agrees`, `is_empty_agrees`: the extracted observers
  compute the model's.
* `sim`: the above, assembled into `Bridge/Queue/Transport.lean`'s `QueueSim` for the extracted
  `BoundedQueue` record instance and `VQ`, related by `toModel s = q`.

No trait assumption appears. The extracted `VecQueue` takes only a `Clone` record, and none of
the bridged operations calls it: `pop` *moves* the element out with `Vec::remove` rather than
cloning it. Every theorem therefore holds at every `Clone` record. Neither `with_capacity` nor `contents` is
a `QueueModel` operation: `with_capacity` is bridged separately (`with_capacity_rel`), `contents`
is not bridged. Every triple here is total correctness, so
each theorem also rules out panic, overflow and divergence of the extracted function.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.vec_queue
open framed_channel

variable {α : Type}

/-- Error agreement: at the bound the extracted `push` returns `Err(Full)` and keeps the queue.
`[EXTRACTED: aeneas + bridge]` -/
theorem push_full (cln : core.clone.Clone α) (s : queue.VecQueue α) (x : α)
    (h : (toModel s).cap ≤ (toModel s).items.length) :
    queue.VecQueue.push cln s x ⦃ p => p = (.Err (), s) ⦄ := by
  simp only [toModel] at h
  unfold queue.VecQueue.push
  step*

/-- Refinement: below the bound the extracted `push` succeeds and abstracts to the model's `push`.
`[EXTRACTED: aeneas + bridge]` -/
theorem push_refines (cln : core.clone.Clone α) (s : queue.VecQueue α) (x : α)
    (h : ¬ (toModel s).cap ≤ (toModel s).items.length) :
    queue.VecQueue.push cln s x
      ⦃ p => p.1 = .Ok () ∧ (toModel s).push x = .ok (toModel p.2) ⦄ := by
  simp only [toModel] at h
  unfold queue.VecQueue.push
  step*
  simp [toModel, FramedChannel.VecQueue.VQ.push, *]

/-- Error agreement: on an empty queue the extracted `pop` returns `None` and keeps the queue.
`[EXTRACTED: aeneas + bridge]` -/
theorem pop_empty (cln : core.clone.Clone α) (s : queue.VecQueue α)
    (h : (toModel s).items = []) :
    queue.VecQueue.pop cln s ⦃ p => p = (none, s) ⦄ := by
  simp only [toModel] at h
  unfold queue.VecQueue.pop queue.VecQueue.is_empty queue.VecQueue.len
  step*

/-- Refinement: on a non-empty queue the extracted `pop` succeeds and abstracts to the model's
`pop`. `[EXTRACTED: aeneas + bridge]` -/
theorem pop_refines (cln : core.clone.Clone α) (s : queue.VecQueue α)
    (h : (toModel s).items ≠ []) :
    queue.VecQueue.pop cln s
      ⦃ p => ∃ y, p.1 = some y ∧ (toModel s).pop = .ok (y, toModel p.2) ⦄ := by
  simp only [toModel] at h
  unfold queue.VecQueue.pop queue.VecQueue.is_empty queue.VecQueue.len
  step*
  · simp_all [alloc.vec.Vec.len]
  · refine ⟨_, rfl, ?_⟩
    obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil h
    simp_all [toModel, FramedChannel.VecQueue.VQ.pop]

/-- The extracted `capacity` is the model's bound. `[EXTRACTED: aeneas + bridge]` -/
theorem capacity_agrees (cln : core.clone.Clone α) (s : queue.VecQueue α) :
    queue.VecQueue.capacity cln s ⦃ c => c.val = (toModel s).cap ⦄ := by
  unfold queue.VecQueue.capacity
  simp [toModel]

/-- The extracted `len` is the model's item count. `[EXTRACTED: aeneas + bridge]` -/
theorem len_agrees (cln : core.clone.Clone α) (s : queue.VecQueue α) :
    queue.VecQueue.len cln s ⦃ n => n.val = (toModel s).items.length ⦄ := by
  unfold queue.VecQueue.len
  simp [toModel]

/-- The extracted `is_full` is the model's bound check. `[EXTRACTED: aeneas + bridge]` -/
theorem is_full_agrees (cln : core.clone.Clone α) (s : queue.VecQueue α) :
    queue.VecQueue.is_full cln s
      ⦃ b => b = decide ((toModel s).cap ≤ (toModel s).items.length) ⦄ := by
  unfold queue.VecQueue.is_full
  simp [toModel]

/-- The extracted `is_empty` is the model's emptiness check. `[EXTRACTED: aeneas + bridge]` -/
theorem is_empty_agrees (cln : core.clone.Clone α) (s : queue.VecQueue α) :
    queue.VecQueue.is_empty cln s ⦃ b => b = (toModel s).items.isEmpty ⦄ := by
  unfold queue.VecQueue.is_empty queue.VecQueue.len
  simp only [toModel]
  simp [UScalar.eq_equiv]
  exact Bool.eq_iff_iff.mpr (by simp)

/-- The extracted `BoundedQueue` record instance of the list-backed queue simulates the model
`VQ`, related by `toModel s = q`, at every `Clone` record: the per-component input to every
generic transport theorem in `Bridge/Queue/Transport.lean`. `[EXTRACTED: aeneas + bridge]` -/
theorem sim (cln : core.clone.Clone α) :
    QueueSim (queue.VecQueue α) (FramedChannel.VecQueue.VQ α) α
      (queue.VecQueue.Insts.Framed_channelQueueBoundedQueue cln)
      (fun s q => toModel s = q) where
  push_ok s q x hR h := by
    subst hR
    apply WP.spec_mono (push_refines cln s x (by simpa [QueueModel.full] using h))
    rintro ⟨e, s'⟩ ⟨he, hs'⟩
    exact ⟨he, toModel s', hs', rfl⟩
  push_full s q x hR h := by
    subst hR
    exact push_full cln s x (by simpa [QueueModel.full] using h)
  pop_ok s q hR h := by
    subst hR
    apply WP.spec_mono (pop_refines cln s (by simpa [QueueModel.empty] using h))
    rintro ⟨o, s'⟩ ⟨y, hy, hs'⟩
    exact ⟨y, toModel s', hy, hs', rfl⟩
  pop_empty s q hR h := by
    subst hR
    exact pop_empty cln s (by simpa [QueueModel.empty] using h)
  len s q hR := by
    apply WP.spec_mono (len_agrees cln s)
    intro n hn
    rw [hn, hR]
    rfl
  capacity s q hR := by
    apply WP.spec_mono (capacity_agrees cln s)
    intro c hc
    rw [hc, hR]
    rfl
  is_full s q hR := by
    apply WP.spec_mono (is_full_agrees cln s)
    intro b hb
    rw [hb, hR]
    rfl
  is_empty s q hR := by
    apply WP.spec_mono (is_empty_agrees cln s)
    intro b hb
    rw [hb, hR]
    rfl

/-- `with_capacity` (not a `QueueModel` operation, so not part of `sim`): the new queue is
empty with capacity exactly `cap` (no rounding). The channel bridge starts from it.
`[EXTRACTED: aeneas + bridge]` -/
theorem with_capacity_rel (cln : core.clone.Clone α) (cap : Usize) :
    queue.VecQueue.with_capacity cln cap ⦃ s => toModel s = { items := [], cap := cap.val } ⦄ := by
  simp [queue.VecQueue.with_capacity, toModel]

/-- `push_law` for the extracted code, derived from the generic transport: below the bound the
extracted `push` succeeds and appends to the model's items. The counterpart of
`ring_buffer.push_law_extracted`, and simpler: no `Inv`, no `Default` record and no `CloneIsId`,
since the extracted `VecQueue` never calls `clone`. `[EXTRACTED: aeneas + bridge]` -/
theorem push_law_extracted (cln : core.clone.Clone α) (s : queue.VecQueue α) (x : α)
    (h : ¬ (toModel s).cap ≤ (toModel s).items.length) :
    queue.VecQueue.push cln s x
      ⦃ p => p.1 = .Ok () ∧ (toModel p.2).items = (toModel s).items ++ [x] ⦄ := by
  have ht := push_law_of_sim (sim cln) s (toModel s) x rfl
    (by simpa [QueueModel.full] using h)
  apply WP.spec_mono ht
  rintro p ⟨he, q', hR', hl⟩
  exact ⟨he, by rw [hR']; exact hl⟩

/-- `pop_law` for the extracted code, derived from the generic transport: on a non-empty queue the
extracted `pop` succeeds and removes the front of the model's items. The counterpart of
`ring_buffer.pop_law_extracted`. `[EXTRACTED: aeneas + bridge]` -/
theorem pop_law_extracted (cln : core.clone.Clone α) (s : queue.VecQueue α)
    (h : (toModel s).items ≠ []) :
    queue.VecQueue.pop cln s
      ⦃ p => ∃ y, p.1 = some y ∧ (toModel s).items = y :: (toModel p.2).items ⦄ := by
  have ht := pop_law_of_sim (sim cln) s (toModel s) rfl
    (by simpa [QueueModel.empty] using h)
  apply WP.spec_mono ht
  rintro p ⟨y, q', hy, hR', hl⟩
  exact ⟨y, hy, by rw [hR']; exact hl⟩

end FramedChannel.Bridge.vec_queue

#print axioms FramedChannel.Bridge.vec_queue.push_full
#print axioms FramedChannel.Bridge.vec_queue.push_refines
#print axioms FramedChannel.Bridge.vec_queue.pop_empty
#print axioms FramedChannel.Bridge.vec_queue.pop_refines
#print axioms FramedChannel.Bridge.vec_queue.capacity_agrees
#print axioms FramedChannel.Bridge.vec_queue.len_agrees
#print axioms FramedChannel.Bridge.vec_queue.is_full_agrees
#print axioms FramedChannel.Bridge.vec_queue.is_empty_agrees
#print axioms FramedChannel.Bridge.vec_queue.sim
#print axioms FramedChannel.Bridge.vec_queue.with_capacity_rel
#print axioms FramedChannel.Bridge.vec_queue.push_law_extracted
#print axioms FramedChannel.Bridge.vec_queue.pop_law_extracted
