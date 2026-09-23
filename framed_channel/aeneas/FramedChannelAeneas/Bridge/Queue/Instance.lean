-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Transport

/-!
# Bridge/Queue/Instance: `BoundedQueueLaws` on an extracted carrier, from any simulation

`[HAND-WRITTEN]` -- one generic construction that turns a `QueueSim` (`Bridge/Queue/Transport.lean`) into an
instance of the specification's own `QueueModel`/`BoundedQueueLaws` classes whose carrier is the
*extracted* state type.

## The carrier

`Ext S Q T inst R` is the subtype of extracted states `s : S` that are related to *some* model
state, `{s : S // ∃ q, R s q}`. For the ring buffer this is "extracted buffers whose abstraction
satisfies the model's invariant"; for the list-backed queue every extracted state qualifies.

## The operations are the extracted ones

`push`, `pop`, `full`, `empty` and `capacity` run the extracted record's methods and read their
outcome through Aeneas's `Result.match` (Aeneas's `Result` is not an inductive, so it cannot be
pattern-matched directly). A refusal (`Err(Full)`, `None`) and any failure of the extracted code
become the specification's `.fail`. Only `toList` goes through the model: it is the abstraction,
and has no extracted counterpart (`contents` is not a `QueueModel` operation). It is read off the
related model state chosen by `Classical.choose`, which is well defined once `R` is functional.

## The laws are derived, not re-proved

`QueueSim.boundedQueueLaws` proves the six laws from the simulation and the functionality of `R`
alone, each through its generic transport theorem in `Bridge/Queue/Transport.lean` (`push_law_of_sim`,
`pop_law_of_sim`, `full_law_of_sim`, `empty_law_of_sim`, `not_full_of_lt_of_sim`,
`push_capacity_of_sim`). A component bridge supplies one `QueueSim` and one functionality lemma and
obtains an instance on its extracted carrier (`Bridge/RingBuffer/Instance.lean`,
`Bridge/VecQueue/Instance.lean`).
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge
open framed_channel

variable {S Q T : Type} [QueueModel Q T] {inst : queue.BoundedQueue S T} {R : S → Q → Prop}

/-! ## Reading the lowered operations through a related model state -/

theorem extToList_eq (hfun : ∀ s q q', R s q → R s q' → q = q') (s : Ext S Q T inst R) (q : Q)
    (hR : R s.1 q) :
    QueueModel.toList (Q := Ext S Q T inst R) (α := T) s = QueueModel.toList (Q := Q) (α := T) q := by
  show QueueModel.toList (Q := Q) (α := T) (Classical.choose s.2) = _
  rw [hfun _ _ _ (Classical.choose_spec s.2) hR]

theorem extFull_eq (hsim : QueueSim S Q T inst R) (s : Ext S Q T inst R) (q : Q) (hR : R s.1 q) :
    QueueModel.full (Q := Ext S Q T inst R) (α := T) s = QueueModel.full (Q := Q) (α := T) q := by
  obtain ⟨b, hb, hbq⟩ := (WP.spec_equiv_exists _ _).mp (hsim.is_full s.1 q hR)
  show extFull s = _
  simp only [extFull, hb, Result.match.ok, hbq]

theorem extEmpty_eq (hsim : QueueSim S Q T inst R) (s : Ext S Q T inst R) (q : Q) (hR : R s.1 q) :
    QueueModel.empty (Q := Ext S Q T inst R) (α := T) s = QueueModel.empty (Q := Q) (α := T) q := by
  obtain ⟨b, hb, hbq⟩ := (WP.spec_equiv_exists _ _).mp (hsim.is_empty s.1 q hR)
  show extEmpty s = _
  simp only [extEmpty, hb, Result.match.ok, hbq]

theorem extCapacity_eq (hsim : QueueSim S Q T inst R) (s : Ext S Q T inst R) (q : Q)
    (hR : R s.1 q) :
    QueueModel.capacity (Q := Ext S Q T inst R) (α := T) s =
      QueueModel.capacity (Q := Q) (α := T) q := by
  obtain ⟨c, hc, hcq⟩ := (WP.spec_equiv_exists _ _).mp (hsim.capacity s.1 q hR)
  show extCapacity s = _
  simp only [extCapacity, hc, Result.match.ok, hcq]

/-- On a full carrier state the lowered push refuses: the extracted push returned `Err(Full)`. -/
theorem extPush_of_full [BoundedQueueLaws Q T] (hsim : QueueSim S Q T inst R) (s : Ext S Q T inst R)
    (x : T) (h : QueueModel.full (Q := Ext S Q T inst R) (α := T) s) :
    QueueModel.push s x = (.fail : FramedChannel.Result (Ext S Q T inst R)) := by
  obtain ⟨q, hq⟩ := s.2
  rw [extFull_eq hsim s q hq] at h
  obtain ⟨p, hps, hp, -⟩ := (WP.spec_equiv_exists _ _).mp (full_law_of_sim hsim s.1 q x hq h)
  subst hp
  show extPush s x = _
  simp only [extPush, hps, Result.match.ok]

/-- Every simulating extracted record, read on its extracted carrier, satisfies all six bounded-queue
laws, provided the simulation relation is functional. Each law is the matching transport theorem of
`Bridge/Queue/Transport.lean`. `[EXTRACTED: aeneas + bridge]` -/
theorem QueueSim.boundedQueueLaws [BoundedQueueLaws Q T] (hsim : QueueSim S Q T inst R)
    (hfun : ∀ s q q', R s q → R s q' → q = q') : BoundedQueueLaws (Ext S Q T inst R) T where
  push_law s x h := by
    obtain ⟨q, hq⟩ := s.2
    rw [extFull_eq hsim s q hq] at h
    obtain ⟨p, hps, he, q', hR', hl⟩ := (WP.spec_equiv_exists _ _).mp (push_law_of_sim hsim s.1 q x hq h)
    obtain ⟨e, s'⟩ := p
    simp only at he hR' hl
    subst he
    refine ⟨⟨s', q', hR'⟩, ?_, ?_⟩
    · show extPush s x = _
      simp only [extPush, hps, Result.match.ok]
      rw [dif_pos ⟨q', hR'⟩]
    · rw [extToList_eq hfun (⟨s', q', hR'⟩ : Ext S Q T inst R) q' hR', extToList_eq hfun s q hq]
      exact hl
  pop_law s h := by
    obtain ⟨q, hq⟩ := s.2
    rw [extEmpty_eq hsim s q hq] at h
    obtain ⟨p, hps, y, q', hy, hR', hl⟩ := (WP.spec_equiv_exists _ _).mp (pop_law_of_sim hsim s.1 q hq h)
    obtain ⟨o, s'⟩ := p
    simp only at hy hR'
    subst hy
    refine ⟨y, ⟨s', q', hR'⟩, ?_, ?_⟩
    · show extPop s = _
      simp only [extPop, hps, Result.match.ok]
      rw [dif_pos ⟨q', hR'⟩]
    · rw [extToList_eq hfun (⟨s', q', hR'⟩ : Ext S Q T inst R) q' hR', extToList_eq hfun s q hq]
      exact hl
  full_law s x h := extPush_of_full hsim s x h
  empty_law s h := by
    obtain ⟨q, hq⟩ := s.2
    rw [extEmpty_eq hsim s q hq] at h
    obtain ⟨p, hps, hp, -⟩ := (WP.spec_equiv_exists _ _).mp (empty_law_of_sim hsim s.1 q hq h)
    subst hp
    show extPop s = _
    simp only [extPop, hps, Result.match.ok]
  not_full_of_lt s h := by
    obtain ⟨q, hq⟩ := s.2
    rw [extToList_eq hfun s q hq, extCapacity_eq hsim s q hq] at h
    obtain ⟨b, hb, hbf⟩ := (WP.spec_equiv_exists _ _).mp (not_full_of_lt_of_sim hsim s.1 q hq h)
    show ¬ extFull s = true
    simp only [extFull, hb, Result.match.ok, hbf]
    decide
  push_capacity s x s' h := by
    obtain ⟨q, hq⟩ := s.2
    by_cases hf : QueueModel.full (Q := Q) (α := T) q
    · rw [← extFull_eq hsim s q hq] at hf
      rw [extPush_of_full hsim s x hf] at h
      exact absurd h (by simp)
    · obtain ⟨p, hps, q', hR', hcap⟩ :=
        (WP.spec_equiv_exists _ _).mp (push_capacity_of_sim hsim s.1 q x hq hf)
      obtain ⟨p', hps', he, -⟩ := (WP.spec_equiv_exists _ _).mp (push_law_of_sim hsim s.1 q x hq hf)
      rw [hps] at hps'
      obtain rfl := Result.ok_injective hps'
      obtain ⟨e, s''⟩ := p
      simp only at he hR' hcap
      subst he
      change extPush s x = .ok s' at h
      simp only [extPush, hps, Result.match.ok] at h
      rw [dif_pos ⟨q', hR'⟩] at h
      cases h
      rw [extCapacity_eq hsim _ q' hR', extCapacity_eq hsim s q hq]
      exact hcap

end FramedChannel.Bridge

#print axioms FramedChannel.Bridge.extToList_eq
#print axioms FramedChannel.Bridge.extFull_eq
#print axioms FramedChannel.Bridge.extEmpty_eq
#print axioms FramedChannel.Bridge.extCapacity_eq
#print axioms FramedChannel.Bridge.extPush_of_full
#print axioms FramedChannel.Bridge.QueueSim.boundedQueueLaws
