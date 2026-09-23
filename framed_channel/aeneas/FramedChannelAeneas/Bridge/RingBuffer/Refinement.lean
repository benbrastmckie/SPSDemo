-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Traits
import FramedChannelAeneas.Bridge.Queue.Transport
import FramedChannelAeneas.Bridge.RingBuffer.Defs
import FramedChannel.Model.RingBuffer.Theorems

/-!
# Bridge/RingBuffer/Refinement: the extracted ring buffer refines the hand-written model

`[EXTRACTED: aeneas + bridge]` -- kernel-checked theorems connecting the Charon/Aeneas
extraction of `rust/src/ring_buffer.rs` (`Extracted/Funs.lean`, generated, never hand-edited) to
`FramedChannel.RingBuffer` (`lean/FramedChannel/Model/RingBuffer/Theorems.lean`, hand-written), through
`toModel` (`Defs.lean` beside this file).

* `push_full`, `pop_empty`: on a full (empty) buffer the extracted `push` (`pop`) returns
  `Err(Full)` (`None`) and leaves the buffer unchanged -- the model's `.fail` branch.
* `push_refines`, `pop_refines`: otherwise, under the model's `Inv`, the extracted operation
  succeeds and its result abstracts to exactly what the model's `push`/`pop` returns.
* `capacity_agrees`, `is_full_agrees`, `is_empty_agrees`, `len_agrees`: the extracted observers
  compute the model's.
* `sim`: the above, assembled into `Bridge/Queue/Transport.lean`'s `QueueSim` for the extracted
  `BoundedQueue` record instance and the model's invariant subtype `BQ`, related by
  `toModel s = q.1`. Through the generic transport theorems, the extracted record therefore
  satisfies all six `BoundedQueueLaws`.
* `push_law_extracted`, `pop_law_extracted`: the queue laws stated directly over the extracted
  `push`/`pop` (they preserve `Inv` and act on `contents` as a FIFO queue), derived as
  corollaries of `push_law_of_sim`/`pop_law_of_sim` at `sim`.

Every theorem quantifies over any `Default` record and any `Clone` record with `CloneIsId`; see
`Bridge/Queue/Traits.lean`. `push_law_extracted` needs no `CloneIsId`: the extracted `push` never calls
`clone`, so it is the same function at every `Clone` record, and the transport is taken at the
canonical `cln`. `with_capacity` is bridged separately (`with_capacity_rel`), since it is not a
`QueueModel` operation. Not bridged: `contents` (a `loop` in the extraction; the
model's `contents` is the abstraction instead). The extractor itself (rustc MIR, Charon, Aeneas,
and Aeneas's `Vec`/`Usize` library models) is trusted, not verified.

Every declaration's `#print axioms` is at the end of this file; `../../../check.sh --aeneas`
audits them with the same gate as the core package.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.ring_buffer
open framed_channel

variable {α : Type}

/-- `[EXTRACTED: aeneas + bridge]` -/
theorem push_full (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) (x : α) (h : (toModel r).full) :
    ring_buffer.RingBuffer.push dflt cln r x ⦃ p => p = (.Err (), r) ⦄ := by
  simp only [toModel, FramedChannel.RingBuffer.full, beq_iff_eq] at h
  unfold ring_buffer.RingBuffer.push
  step*

theorem set_opt_some (l : List α) (n : Nat) (x : α) : l.set_opt n (some x) = l.set n x := by
  induction l generalizing n with
  | nil => simp [List.set_opt]
  | cons y tl ih => cases n <;> simp [List.set_opt, ih]

@[step]
theorem set_spec (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) (i : Usize) (x : α) (hi : i.val < r.buf.val.length) :
    ring_buffer.RingBuffer.set dflt cln r i x
      ⦃ r' => r'.buf.val = r.buf.val.set i.val x ∧ r'.head = r.head ∧ r'.tail = r.tail ∧
        r'.len = r.len ⦄ := by
  unfold ring_buffer.RingBuffer.set
  simp only [lift, alloc.vec.Vec.deref_mut]
  have hs : i.val < r.buf.slice.val.length := hi
  simp [core.slice.Slice.get_mut, Slice.set_opt]
  rw [List.getElem?_eq_getElem hs]
  simp only [WP.spec_ok, alloc.vec.Vec.val, Slice.from_val, and_true]
  exact set_opt_some _ _ _

@[step]
theorem get_spec [Inhabited α] (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (hcln : CloneIsId cln) (r : ring_buffer.RingBuffer α) (i : Usize)
    (hi : i.val < r.buf.val.length) :
    ring_buffer.RingBuffer.get dflt cln r i ⦃ y => y = r.buf.val.getD i.val default ⦄ := by
  unfold ring_buffer.RingBuffer.get
  have hs : i.val < r.buf.slice.val.length := hi
  simp [core.slice.Slice.get, alloc.vec.Vec.deref]
  rw [List.getElem?_eq_getElem hi]
  simp [hcln _]

/-- `[EXTRACTED: aeneas + bridge]` -/
theorem push_refines (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) (x : α) (hInv : (toModel r).Inv) (h : ¬ (toModel r).full) :
    ring_buffer.RingBuffer.push dflt cln r x
      ⦃ p => p.1 = .Ok () ∧ (toModel r).push x = .ok (toModel p.2) ⦄ := by
  simp only [toModel, FramedChannel.RingBuffer.full, beq_iff_eq] at h
  obtain ⟨h0, hlen, hhead, htail⟩ := hInv
  simp only [toModel] at h0 hlen hhead htail
  have htl : r.tail.val < r.buf.val.length := by rw [htail]; exact Nat.mod_lt _ h0
  unfold ring_buffer.RingBuffer.push
  step*
  simp only [toModel, FramedChannel.RingBuffer.push, beq_iff_eq, h, if_false,
    FramedChannel.Result.ok.injEq, FramedChannel.RingBuffer.mk.injEq]
  simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at i2_post
  refine ⟨self1_post.symm, ?_, ?_, ?_⟩
  · rw [self1_post1]
  · rw [i2_post, i1_post, self1_post2]
  · rw [i3_post, self1_post3]

/-- `[EXTRACTED: aeneas + bridge]` -/
theorem pop_empty (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) (h : (toModel r).empty) :
    ring_buffer.RingBuffer.pop dflt cln r ⦃ p => p = (none, r) ⦄ := by
  simp only [toModel, FramedChannel.RingBuffer.empty, beq_iff_eq] at h
  unfold ring_buffer.RingBuffer.pop
  step*

/-- `[EXTRACTED: aeneas + bridge]` -/
theorem pop_refines [Inhabited α] (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (hcln : CloneIsId cln) (r : ring_buffer.RingBuffer α)
    (hInv : (toModel r).Inv) (h : ¬ (toModel r).empty) :
    ring_buffer.RingBuffer.pop dflt cln r
      ⦃ p => ∃ y, p.1 = some y ∧ (toModel r).pop = .ok (y, toModel p.2) ⦄ := by
  simp only [toModel, FramedChannel.RingBuffer.empty, beq_iff_eq] at h
  obtain ⟨h0, hlen, hhead, htail⟩ := hInv
  simp only [toModel] at h0 hlen hhead htail
  unfold ring_buffer.RingBuffer.pop
  step*
  refine ⟨x, rfl, ?_⟩
  simp only [toModel, FramedChannel.RingBuffer.pop, beq_iff_eq, h, if_false,
    FramedChannel.Result.ok.injEq, Prod.mk.injEq, FramedChannel.RingBuffer.mk.injEq]
  simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at i1_post
  exact ⟨x_post.symm, trivial, by rw [i1_post, i_post], trivial, i2_post.symm⟩

/-- `[EXTRACTED: aeneas + bridge]` -/
theorem capacity_agrees (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) :
    ring_buffer.RingBuffer.capacity dflt cln r ⦃ c => c.val = (toModel r).buf.length ⦄ := by
  unfold ring_buffer.RingBuffer.capacity
  simp [toModel]

/-- `[EXTRACTED: aeneas + bridge]` -/
theorem is_full_agrees (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) :
    ring_buffer.RingBuffer.is_full dflt cln r ⦃ b => b = (toModel r).full ⦄ := by
  unfold ring_buffer.RingBuffer.is_full
  simp only [toModel, FramedChannel.RingBuffer.full]
  simp [UScalar.eq_equiv]
  exact Bool.eq_iff_iff.mpr (by simp)

/-- `[EXTRACTED: aeneas + bridge]` -/
theorem is_empty_agrees (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) :
    ring_buffer.RingBuffer.is_empty dflt cln r ⦃ b => b = (toModel r).empty ⦄ := by
  unfold ring_buffer.RingBuffer.is_empty
  simp only [toModel, FramedChannel.RingBuffer.empty]
  simp [UScalar.eq_equiv]
  exact Bool.eq_iff_iff.mpr (by simp)

/-- The observer the transport's `len` field needs: the extracted `len` is the model's count.
`[EXTRACTED: aeneas + bridge]` -/
theorem len_agrees (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) :
    ring_buffer.RingBuffer.impl.len dflt cln r ⦃ n => n.val = (toModel r).len ⦄ := by
  unfold ring_buffer.RingBuffer.impl.len
  simp [toModel]

/-- A successful model `push` on the carrier of a `BQ` value is the `BQ` operation's result. -/
theorem pushBQ_of_push [Inhabited α] (q : FramedChannel.RingBuffer.BQ α) (x : α)
    (r' : FramedChannel.RingBuffer α) (hp : q.1.push x = .ok r') :
    ∃ q', FramedChannel.RingBuffer.pushBQ q x = .ok q' ∧ q'.1 = r' := by
  have hf : ¬ q.1.full := by
    intro hfull
    rw [FramedChannel.RingBuffer.push_fail α q.1 x hfull] at hp
    exact absurd hp (by simp)
  unfold FramedChannel.RingBuffer.pushBQ
  rw [dif_neg hf]
  split
  · rename_i r'' hp'
    rw [hp] at hp'
    cases hp'
    exact ⟨_, rfl, rfl⟩
  · rename_i hp'
    rw [hp] at hp'
    exact absurd hp' (by simp)

/-- A successful model `pop` on the carrier of a `BQ` value is the `BQ` operation's result. -/
theorem popBQ_of_pop [Inhabited α] (q : FramedChannel.RingBuffer.BQ α) (y : α)
    (r' : FramedChannel.RingBuffer α) (hp : q.1.pop = .ok (y, r')) :
    ∃ q', FramedChannel.RingBuffer.popBQ q = .ok (y, q') ∧ q'.1 = r' := by
  have he : ¬ q.1.empty := by
    intro hempty
    rw [FramedChannel.RingBuffer.pop_fail α q.1 hempty] at hp
    exact absurd hp (by simp)
  unfold FramedChannel.RingBuffer.popBQ
  rw [dif_neg he]
  split
  · rename_i z r'' hp'
    rw [hp] at hp'
    cases hp'
    exact ⟨_, rfl, rfl⟩
  · rename_i hp'
    rw [hp] at hp'
    exact absurd hp' (by simp)

/-- The extracted `BoundedQueue` record instance of the ring buffer simulates the model's
invariant subtype `BQ`, related by `toModel s = q.1`: the per-component input to every generic
transport theorem in `Bridge/Queue/Transport.lean`. `[EXTRACTED: aeneas + bridge]` -/
theorem sim {α : Type} [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) (hcln : CloneIsId cln) :
    QueueSim (ring_buffer.RingBuffer α) (FramedChannel.RingBuffer.BQ α) α
      (ring_buffer.RingBuffer.Insts.Framed_channelQueueBoundedQueue dflt cln)
      (fun s q => toModel s = q.1) where
  push_ok s q x hR h := by
    have hInv : (toModel s).Inv := by rw [hR]; exact q.2
    have hf : ¬ (toModel s).full := by rw [hR]; exact h
    apply WP.spec_mono (push_refines dflt cln s x hInv hf)
    rintro ⟨e, s'⟩ ⟨he, hs'⟩
    rw [hR] at hs'
    obtain ⟨q', hq', hval⟩ := pushBQ_of_push q x (toModel s') hs'
    exact ⟨he, q', hq', hval.symm⟩
  push_full s q x hR h := push_full dflt cln s x (by rw [hR]; exact h)
  pop_ok s q hR h := by
    have hInv : (toModel s).Inv := by rw [hR]; exact q.2
    have he : ¬ (toModel s).empty := by rw [hR]; exact h
    apply WP.spec_mono (pop_refines dflt cln hcln s hInv he)
    rintro ⟨o, s'⟩ ⟨y, hy, hs'⟩
    rw [hR] at hs'
    obtain ⟨q', hq', hval⟩ := popBQ_of_pop q y (toModel s') hs'
    exact ⟨y, q', hy, hq', hval.symm⟩
  pop_empty s q hR h := pop_empty dflt cln s (by rw [hR]; exact h)
  len s q hR := by
    apply WP.spec_mono (len_agrees dflt cln s)
    intro n hn
    rw [hn, hR]
    show q.1.len = q.1.contents.length
    simp [FramedChannel.RingBuffer.contents]
  capacity s q hR := by
    apply WP.spec_mono (capacity_agrees dflt cln s)
    intro c hc
    rw [hc, hR]
    rfl
  is_full s q hR := by
    apply WP.spec_mono (is_full_agrees dflt cln s)
    intro b hb
    rw [hb, hR]
    rfl
  is_empty s q hR := by
    apply WP.spec_mono (is_empty_agrees dflt cln s)
    intro b hb
    rw [hb, hR]
    rfl

/-- `push_law` for the extracted code, derived from the generic transport: the extracted `push`
preserves `Inv` and appends to `contents`. `[EXTRACTED: aeneas + bridge]` -/
theorem push_law_extracted [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) (r : ring_buffer.RingBuffer α) (x : α)
    (hInv : (toModel r).Inv) (h : ¬ (toModel r).full) :
    ring_buffer.RingBuffer.push dflt cln r x
      ⦃ p => p.1 = .Ok () ∧ (toModel p.2).Inv ∧
        (toModel p.2).contents = (toModel r).contents ++ [x] ⦄ := by
  -- The extracted `push` never calls `clone`, so it is definitionally the same function at the
  -- canonical `Clone` record, where `sim`'s `CloneIsId` holds by `cln_isId`.
  have hsim := sim (α := α) dflt FramedChannel.Bridge.cln FramedChannel.Bridge.cln_isId
  have ht := push_law_of_sim hsim r ⟨toModel r, hInv⟩ x rfl h
  change ring_buffer.RingBuffer.push dflt FramedChannel.Bridge.cln r x ⦃ _ ⦄ at ht
  change ring_buffer.RingBuffer.push dflt FramedChannel.Bridge.cln r x ⦃ _ ⦄
  apply WP.spec_mono ht
  rintro p ⟨he, q', hR', hl⟩
  refine ⟨he, by rw [hR']; exact q'.2, ?_⟩
  rw [hR']
  exact hl

/-- `pop_law` for the extracted code, derived from the generic transport: the extracted `pop`
preserves `Inv` and removes the front of `contents`. `[EXTRACTED: aeneas + bridge]` -/
theorem pop_law_extracted [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) (hcln : CloneIsId cln) (r : ring_buffer.RingBuffer α)
    (hInv : (toModel r).Inv) (h : ¬ (toModel r).empty) :
    ring_buffer.RingBuffer.pop dflt cln r
      ⦃ p => ∃ y, p.1 = some y ∧ (toModel p.2).Inv ∧
        (toModel r).contents = y :: (toModel p.2).contents ⦄ := by
  have ht := pop_law_of_sim (sim dflt cln hcln) r ⟨toModel r, hInv⟩ rfl h
  apply WP.spec_mono ht
  rintro p ⟨y, q', hy, hR', hl⟩
  refine ⟨y, hy, by rw [hR']; exact q'.2, ?_⟩
  rw [hR']
  exact hl

/-- `with_capacity` (not a `QueueModel` operation, so not part of `sim`): the new buffer
satisfies the model's invariant, is empty, and has capacity `cap` rounded up to 1, for any
`Default` record that returns and any identity `Clone`. The channel bridge starts from it.
`[EXTRACTED: aeneas + bridge]` -/
theorem with_capacity_rel (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (hcln : CloneIsId cln) (x : α) (hx : dflt.default = ok x) (cap : Usize) :
    ring_buffer.RingBuffer.with_capacity dflt cln cap
      ⦃ s => (toModel s).Inv ∧ (toModel s).len = 0 ∧ (toModel s).buf.length = max cap.val 1 ⦄ := by
  unfold ring_buffer.RingBuffer.with_capacity
  by_cases h0 : cap = 0#usize
  · simp only [h0, if_true, bind_tc_ok, hx]
    step with alloc.vec.from_elem_spec cln x 1#usize (hcln x) as ⟨v, hv1, hv2⟩
    simp [toModel, FramedChannel.RingBuffer.Inv, hv1]
  · simp only [h0, if_false, bind_tc_ok, hx]
    step with alloc.vec.from_elem_spec cln x cap (hcln x) as ⟨v, hv1, hv2⟩
    have : cap.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simpa using h))
    simp [toModel, FramedChannel.RingBuffer.Inv, hv1]
    omega

end FramedChannel.Bridge.ring_buffer

#print axioms FramedChannel.Bridge.ring_buffer.push_full
#print axioms FramedChannel.Bridge.ring_buffer.set_opt_some
#print axioms FramedChannel.Bridge.ring_buffer.set_spec
#print axioms FramedChannel.Bridge.ring_buffer.get_spec
#print axioms FramedChannel.Bridge.ring_buffer.push_refines
#print axioms FramedChannel.Bridge.ring_buffer.pop_empty
#print axioms FramedChannel.Bridge.ring_buffer.pop_refines
#print axioms FramedChannel.Bridge.ring_buffer.capacity_agrees
#print axioms FramedChannel.Bridge.ring_buffer.is_full_agrees
#print axioms FramedChannel.Bridge.ring_buffer.is_empty_agrees
#print axioms FramedChannel.Bridge.ring_buffer.len_agrees
#print axioms FramedChannel.Bridge.ring_buffer.pushBQ_of_push
#print axioms FramedChannel.Bridge.ring_buffer.popBQ_of_pop
#print axioms FramedChannel.Bridge.ring_buffer.sim
#print axioms FramedChannel.Bridge.ring_buffer.push_law_extracted
#print axioms FramedChannel.Bridge.ring_buffer.pop_law_extracted
#print axioms FramedChannel.Bridge.ring_buffer.with_capacity_rel
