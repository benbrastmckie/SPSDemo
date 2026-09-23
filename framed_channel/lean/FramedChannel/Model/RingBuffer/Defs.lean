-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Queue

/-!
# Model/RingBuffer/Defs: the ring-buffer definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of `Model/RingBuffer/Theorems.lean`: the
representation, its invariant, the operations, the invariant subtype `BQ` and the `QueueModel`
instance on it. The theorems about them live in `Model/RingBuffer/Theorems.lean`. This module holds
definitions only, so that the Challenge module `FramedChannelChallenge.RingBuffer` can import them
without importing a registered theorem.

One documented exception: `pushBQ` and `popBQ` build the invariant subtype with `push_inv` and
`pop_inv`, so those two theorems (and the `inv_preserve` seed tactic `pop_inv` is proved by) live
here with their proofs. They stay registered rows, and `certificate/policy.txt` lists them as the
`shared-proof` pair: the specification imports these two proved constants rather than restating
them.
-/
namespace FramedChannel

structure RingBuffer (α : Type) where
  buf : List α
  head : Nat
  tail : Nat
  len : Nat

namespace RingBuffer

/-- Representation invariant: non-empty storage, count within capacity, read index in range,
write index derived from the read index and the count. -/
def Inv {α : Type} (r : RingBuffer α) : Prop :=
  0 < r.buf.length ∧ r.len ≤ r.buf.length ∧ r.head < r.buf.length ∧
    r.tail = (r.head + r.len) % r.buf.length

def full {α : Type} (r : RingBuffer α) : Bool := r.len == r.buf.length

def empty {α : Type} (r : RingBuffer α) : Bool := r.len == 0

/-- The abstraction function (the interface's `toList`): the logical FIFO sequence, read as a
`len`-window from `head` modulo the capacity. -/
def contents {α : Type} [Inhabited α] (r : RingBuffer α) : List α :=
  (List.range r.len).map fun i => r.buf.getD ((r.head + i) % r.buf.length) default

/-- `RingBuffer::push`: fail when full, else write at `tail` and advance it modulo capacity. -/
def push {α : Type} (r : RingBuffer α) (x : α) : Result (RingBuffer α) :=
  if r.len == r.buf.length then .fail
  else .ok { r with buf := r.buf.set r.tail x,
                    tail := (r.tail + 1) % r.buf.length, len := r.len + 1 }

/-- Invariant preservation (the four-conjunct route). `[PROVED: kernel]` -/
theorem push_inv (α : Type) (r : RingBuffer α) (x : α) (hInv : r.Inv) (h : ¬ r.full)
    (r' : RingBuffer α) (hpush : r.push x = .ok r') : r'.Inv := by
  simp only [full, beq_iff_eq] at h
  simp only [push, beq_iff_eq, h, ↓reduceIte, Result.ok.injEq] at hpush
  subst hpush
  obtain ⟨h0, hlen, hhead, htail⟩ := hInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h0
  · simp only [List.length_set]; omega
  · simpa using hhead
  · simp only [List.length_set]
    rw [htail, Nat.mod_add_mod, Nat.add_assoc]

set_option hygiene false in
/-- Replays the invariant-preservation script. The `first` alternatives on conjuncts 3 and 4
are the two hints `pop` needed beyond the `push` script. -/
macro "inv_preserve" hstep:ident : tactic => `(tactic| (
  simp only [full, empty, beq_iff_eq] at h
  simp only [push, pop, beq_iff_eq, h, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at $hstep:ident
  first
    | subst $hstep:ident
    | (obtain ⟨_, $hstep:ident⟩ := $hstep:ident; subst $hstep:ident)
  obtain ⟨h0, hlen, hhead, htail⟩ := hInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h0
  · simp only [List.length_set]; omega
  · first
      | simpa using hhead
      | exact Nat.mod_lt _ h0
  · simp only [List.length_set]
    first
      | (rw [htail, Nat.mod_add_mod, Nat.add_assoc]; done)
      | (rw [htail, Nat.mod_add_mod]; congr 1; omega)))

/-- `RingBuffer::pop`: fail when empty, else read at `head`, advance it modulo capacity, and
decrement the count. -/
def pop {α : Type} [Inhabited α] (r : RingBuffer α) : Result (α × RingBuffer α) :=
  if r.len == 0 then .fail
  else .ok (r.buf.getD r.head default,
            { r with head := (r.head + 1) % r.buf.length, len := r.len - 1 })

/-- Invariant preservation for `pop`. `[PROVED: kernel]` -/
theorem pop_inv (α : Type) [Inhabited α] (r : RingBuffer α) (hInv : r.Inv) (h : ¬ r.empty)
    (x : α) (r' : RingBuffer α) (hpop : r.pop = .ok (x, r')) : r'.Inv := by
  inv_preserve hpop

/-- The invariant subtype: the values the interface instance ranges over. -/
abbrev BQ (α : Type) : Type := { r : RingBuffer α // r.Inv }

/-- `push` on the subtype, carrying `push_inv` for the new value. -/
def pushBQ {α : Type} (q : BQ α) (x : α) : Result (BQ α) :=
  if h : q.1.full then .fail
  else
    match hp : q.1.push x with
    | .ok r' => .ok ⟨r', push_inv α q.1 x q.2 h r' hp⟩
    | .fail => .fail

/-- `pop` on the subtype, carrying `pop_inv` for the new value. -/
def popBQ {α : Type} [Inhabited α] (q : BQ α) : Result (α × BQ α) :=
  if h : q.1.empty then .fail
  else
    match hp : q.1.pop with
    | .ok (x, r') => .ok (x, ⟨r', pop_inv α q.1 q.2 h x r' hp⟩)
    | .fail => .fail

/-- The `QueueModel` operations (L0) on the invariant subtype `BQ α`. -/
instance instQueueModel (α : Type) [Inhabited α] : QueueModel (BQ α) α where
  push := pushBQ
  pop := popBQ
  toList q := q.1.contents
  full q := q.1.full
  empty q := q.1.empty
  capacity q := q.1.buf.length

#print axioms push_inv
#print axioms pop_inv

end RingBuffer

end FramedChannel
