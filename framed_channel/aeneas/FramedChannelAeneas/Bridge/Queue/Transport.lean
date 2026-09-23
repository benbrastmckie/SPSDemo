-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Defs

/-!
# Bridge/Queue/Transport: the queue simulation relation and the generic transport theorems

`[HAND-WRITTEN]` -- how an extracted bounded queue reaches the specification layer's
`BoundedQueueLaws` without an ad hoc wrapper.

## The problem this solves

The laws in `lean/FramedChannel/Spec/Queue.lean` are stated over the specification's own `Result`
and a pure `push : Q → α → Result Q`. The extraction does not have that shape. Charon and Aeneas
turn `rust/src/queue.rs`'s `BoundedQueue<T>` trait into a record of eight functions in Aeneas's
`Result` monad (`queue.BoundedQueue Self T`), whose `push` is state-passing and keeps the state on
refusal: it returns `(Err(Full), self)`, where the model's `push` returns `.fail`. Restating the
laws once per carrier, or making them monad-generic, would duplicate the specification. Instead:

* `QueueSim S Q T inst R` says that the extracted record `inst` over state `S` simulates a model
  `Q` of the L0 interface through a relation `R`, one field per method and per branch, each an
  Aeneas triple. A *relation*, not an abstraction function, because the model carrier may be an
  invariant subtype (`RingBuffer.BQ`) that a raw extracted state does not determine a proof for.
* The six transport theorems below prove, once for every interface instance, that a simulating
  record satisfies each of the six laws, read through `R`. They use only `QueueSim` and
  `BoundedQueueLaws`, never a concrete queue.

A component bridge then proves one `QueueSim` (for the ring buffer, `sim` in
`Bridge/RingBuffer/Refinement.lean`) and inherits all six laws at the extracted code. This is the
per-function claim shape `Faithful impl model -> Refines model spec -> Refines impl spec`, with
`Faithful := QueueSim` and `Refines model spec := BoundedQueueLaws`.

## The obligation this raises for the channel

The extracted `channel.Channel.send` adds `inst.len` to the in-flight count as a `Usize`, so the
channel bridge must show that sum stays within `Usize.max`. `QueueSim.len` and `QueueSim.capacity`
give `len = (toList q).length` and `capacity = QueueModel.capacity q`; the channel invariant bounds
queued plus in-flight by the capacity, which the record reports as a `Usize`. `Bridge/Channel/`
discharges it that way (`hovf_of_inv` in `Composite.lean`), and `send_refines` states it as a
hypothesis only on arbitrary states.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge
open framed_channel

/-- `push_law` at the extracted record: a push on a non-full queue succeeds and appends `x` to the
related model's contents. `[PROVED: kernel]` -/
theorem push_law_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (x : T) (hR : R s q) (h : ¬ QueueModel.full (Q := Q) (α := T) q) :
    inst.push s x ⦃ p => p.1 = .Ok () ∧ ∃ q', R p.2 q' ∧
      QueueModel.toList (Q := Q) (α := T) q' = QueueModel.toList (Q := Q) (α := T) q ++ [x] ⦄ := by
  apply WP.spec_mono (hsim.push_ok s q x hR h)
  rintro p ⟨hp, q', hq', hR'⟩
  obtain ⟨q'', hq'', hl⟩ := BoundedQueueLaws.push_law q x h
  rw [hq'] at hq''
  cases hq''
  exact ⟨hp, q', hR', hl⟩

/-- `pop_law` at the extracted record: a pop on a non-empty queue returns the related model's
front element and its remainder. `[PROVED: kernel]` -/
theorem pop_law_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (hR : R s q) (h : ¬ QueueModel.empty (Q := Q) (α := T) q) :
    inst.pop s ⦃ p => ∃ y q', p.1 = some y ∧ R p.2 q' ∧
      QueueModel.toList (Q := Q) (α := T) q = y :: QueueModel.toList (Q := Q) (α := T) q' ⦄ := by
  apply WP.spec_mono (hsim.pop_ok s q hR h)
  rintro p ⟨y, q', hy, hq', hR'⟩
  obtain ⟨z, q'', hq'', hl⟩ := BoundedQueueLaws.pop_law q h
  rw [hq'] at hq''
  cases hq''
  exact ⟨y, q', hy, hR', hl⟩

/-- `full_law` at the extracted record: on a full queue the extracted push refuses and keeps the
state, exactly where the model's push fails. `[PROVED: kernel]` -/
theorem full_law_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (x : T) (hR : R s q) (h : QueueModel.full (Q := Q) (α := T) q) :
    inst.push s x ⦃ p => p = (.Err (), s) ∧
      QueueModel.push q x = (.fail : FramedChannel.Result Q) ⦄ := by
  apply WP.spec_mono (hsim.push_full s q x hR h)
  intro p hp
  exact ⟨hp, BoundedQueueLaws.full_law q x h⟩

/-- `empty_law` at the extracted record: on an empty queue the extracted pop returns `none` and
keeps the state, exactly where the model's pop fails. `[PROVED: kernel]` -/
theorem empty_law_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (hR : R s q) (h : QueueModel.empty (Q := Q) (α := T) q) :
    inst.pop s ⦃ p => p = (none, s) ∧
      QueueModel.pop q = (.fail : FramedChannel.Result (T × Q)) ⦄ := by
  apply WP.spec_mono (hsim.pop_empty s q hR h)
  intro p hp
  exact ⟨hp, BoundedQueueLaws.empty_law q h⟩

/-- `not_full_of_lt` at the extracted record: room below the capacity means the extracted
`is_full` reports `false`. `[PROVED: kernel]` -/
theorem not_full_of_lt_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (hR : R s q)
    (h : (QueueModel.toList (Q := Q) (α := T) q).length < QueueModel.capacity (Q := Q) (α := T) q) :
    inst.is_full s ⦃ b => b = false ⦄ := by
  apply WP.spec_mono (hsim.is_full s q hR)
  intro b hb
  have hnf := BoundedQueueLaws.not_full_of_lt q h
  rw [hb]
  simpa using hnf

/-- `push_capacity` at the extracted record: a successful extracted push is related to a model
state of the same capacity. `[PROVED: kernel]` -/
theorem push_capacity_of_sim {S Q T : Type} [QueueModel Q T] [BoundedQueueLaws Q T]
    {inst : queue.BoundedQueue S T} {R : S → Q → Prop} (hsim : QueueSim S Q T inst R)
    (s : S) (q : Q) (x : T) (hR : R s q) (h : ¬ QueueModel.full (Q := Q) (α := T) q) :
    inst.push s x ⦃ p => ∃ q', R p.2 q' ∧
      QueueModel.capacity (Q := Q) (α := T) q' = QueueModel.capacity (Q := Q) (α := T) q ⦄ := by
  apply WP.spec_mono (hsim.push_ok s q x hR h)
  rintro p ⟨_, q', hq', hR'⟩
  exact ⟨q', hR', BoundedQueueLaws.push_capacity q x q' hq'⟩

end FramedChannel.Bridge

#print axioms FramedChannel.Bridge.push_law_of_sim
#print axioms FramedChannel.Bridge.pop_law_of_sim
#print axioms FramedChannel.Bridge.full_law_of_sim
#print axioms FramedChannel.Bridge.empty_law_of_sim
#print axioms FramedChannel.Bridge.not_full_of_lt_of_sim
#print axioms FramedChannel.Bridge.push_capacity_of_sim
