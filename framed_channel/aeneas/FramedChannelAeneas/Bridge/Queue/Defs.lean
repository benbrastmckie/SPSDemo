-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs
import FramedChannel.Spec.Queue

/-!
# Bridge/Queue/Defs: the bridge's queue-side definitions

`[HAND-WRITTEN]` -- the definitions every queue bridge statement is stated over:

* the canonical `Default` and `Clone` records `dflt` and `cln`, and the assumption `CloneIsId`
  (used by `Bridge/Queue/Traits.lean`);
* the simulation relation `QueueSim` (used by `Bridge/Queue/Transport.lean`);
* the extracted carrier `Ext`, its lowered operations and the `QueueModel` instance on it (used
  by `Bridge/Queue/Instance.lean`).

It holds definitions only, so that the Challenge module `FramedChannelAeneasChallenge.Queue` can
import them without importing a registered theorem.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge

variable {α : Type}

/-- The canonical `Default` record: `Inhabited.default`. -/
def dflt [Inhabited α] : core.default.Default α := ⟨ok default⟩

/-- The canonical `Clone` record: the identity. -/
def cln : core.clone.Clone α := { clone := ok }

/-- The one assumption the bridge makes about the `Clone` instance. -/
def CloneIsId (c : core.clone.Clone α) : Prop := ∀ v, c.clone v = ok v

end FramedChannel.Bridge

namespace FramedChannel.Bridge
open framed_channel

/-- The extracted bounded-queue record `inst` over state `S` simulates the model `Q` of
`QueueModel` through the relation `R`: every method, on every branch, is related to the model's
operation. -/
structure QueueSim (S Q T : Type) [QueueModel Q T] (inst : queue.BoundedQueue S T)
    (R : S → Q → Prop) : Prop where
  push_ok : ∀ s q x, R s q → ¬ QueueModel.full (Q := Q) (α := T) q →
    inst.push s x ⦃ p => p.1 = .Ok () ∧ ∃ q', QueueModel.push q x = .ok q' ∧ R p.2 q' ⦄
  push_full : ∀ s q x, R s q → QueueModel.full (Q := Q) (α := T) q →
    inst.push s x ⦃ p => p = (.Err (), s) ⦄
  pop_ok : ∀ s q, R s q → ¬ QueueModel.empty (Q := Q) (α := T) q →
    inst.pop s ⦃ p => ∃ y q', p.1 = some y ∧ QueueModel.pop q = .ok (y, q') ∧ R p.2 q' ⦄
  pop_empty : ∀ s q, R s q → QueueModel.empty (Q := Q) (α := T) q →
    inst.pop s ⦃ p => p = (none, s) ⦄
  len : ∀ s q, R s q →
    inst.len s ⦃ n => n.val = (QueueModel.toList (Q := Q) (α := T) q).length ⦄
  capacity : ∀ s q, R s q →
    inst.capacity s ⦃ c => c.val = QueueModel.capacity (Q := Q) (α := T) q ⦄
  is_full : ∀ s q, R s q → inst.is_full s ⦃ b => b = QueueModel.full (Q := Q) (α := T) q ⦄
  is_empty : ∀ s q, R s q → inst.is_empty s ⦃ b => b = QueueModel.empty (Q := Q) (α := T) q ⦄

variable {S Q T : Type} [QueueModel Q T] {inst : queue.BoundedQueue S T} {R : S → Q → Prop}

/-- The extracted carrier: the extracted states related to some model state. The unused
`QueueModel` and record parameters index the carrier by the simulation it is read through. -/
def Ext (S Q T : Type) [QueueModel Q T] (_inst : queue.BoundedQueue S T) (R : S → Q → Prop) :
    Type :=
  {s : S // ∃ q, R s q}

open Classical in
/-- The extracted `push`, lowered: `Ok(())` to `.ok`, `Err(Full)` and every failure to `.fail`. -/
noncomputable def extPush (s : Ext S Q T inst R) (x : T) : FramedChannel.Result (Ext S Q T inst R) :=
  match (inst.push s.1 x).match with
  | .ok (.Ok (), s') => if h : ∃ q, R s' q then .ok ⟨s', h⟩ else .fail
  | _ => .fail

open Classical in
/-- The extracted `pop`, lowered: `Some(y)` to `.ok`, `None` and every failure to `.fail`. -/
noncomputable def extPop (s : Ext S Q T inst R) : FramedChannel.Result (T × Ext S Q T inst R) :=
  match (inst.pop s.1).match with
  | .ok (some y, s') => if h : ∃ q, R s' q then .ok (y, ⟨s', h⟩) else .fail
  | _ => .fail

/-- The extracted `is_full`, lowered (a failing observer reads as full; never reached). -/
noncomputable def extFull (s : Ext S Q T inst R) : Bool :=
  match (inst.is_full s.1).match with
  | .ok b => b
  | _ => true

/-- The extracted `is_empty`, lowered (a failing observer reads as empty; never reached). -/
noncomputable def extEmpty (s : Ext S Q T inst R) : Bool :=
  match (inst.is_empty s.1).match with
  | .ok b => b
  | _ => true

/-- The extracted `capacity`, lowered to its value (a failing observer reads as `0`; never
reached). -/
noncomputable def extCapacity (s : Ext S Q T inst R) : Nat :=
  match (inst.capacity s.1).match with
  | .ok c => c.val
  | _ => 0

/-- The abstraction: the contents of the related model state. -/
noncomputable def extToList (s : Ext S Q T inst R) : List T :=
  QueueModel.toList (Q := Q) (α := T) (Classical.choose s.2)

/-- The `QueueModel` operations on the extracted carrier. -/
noncomputable instance instQueueModelExt (S Q T : Type) [QueueModel Q T]
    (inst : queue.BoundedQueue S T) (R : S → Q → Prop) : QueueModel (Ext S Q T inst R) T where
  push := extPush
  pop := extPop
  toList := extToList
  full := extFull
  empty := extEmpty
  capacity := extCapacity

end FramedChannel.Bridge
