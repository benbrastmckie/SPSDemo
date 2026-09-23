-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Model.RingBuffer.Defs

/-!
# Model/RingBuffer/Theorems: the fully worked component

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/ring_buffer.rs` in the idiom
the Aeneas Lean backend produces: `alloc.vec.Vec` as a `List`, the `Result` monad with a `fail`
branch where the Rust returns `Err(Full)`, and the index arithmetic written out. The aeneas bridge
package proves that the charon/aeneas extraction of `rust/src/ring_buffer.rs` refines `push` and
`pop` below (`aeneas/FramedChannelAeneas/Bridge/RingBuffer/`).

## Rust to Lean field mapping

| Rust `RingBuffer<T>` | Lean `RingBuffer α`  | Note                                    |
|----------------------|----------------------|-----------------------------------------|
| `buf: Vec<T>`        | `buf : List α`       | `buf.len()` is the capacity `cap`       |
| `head: usize`        | `head : Nat`         | read index                              |
| `tail: usize`        | `tail : Nat`         | write index, `= (head + len) % cap`     |
| `len: usize`         | `len : Nat`          | element count, `<= cap`                 |
| `push -> Err(Full)`  | `push = .fail`       | error agreement: `push_fail`            |
| `push -> Ok(())`     | `push = .ok r'`      | `push_ok`, `push_inv`, `push_contents`  |
| `pop -> None`        | `pop = .fail`        | error agreement: `pop_fail`             |
| `pop -> Some(x)`     | `pop = .ok (x, r')`  | `pop_ok`, `pop_inv`, `pop_contents`     |
| `with_capacity(cap)` | (none)               | see below                               |

There is deliberately no Lean counterpart of `with_capacity`. The Rust rounds a zero capacity up
to one, which is exactly what `Inv`'s `0 < buf.length` demands; the model instead takes `Inv` as a
hypothesis and every theorem below carries it, so the rounding has nothing to correspond to. The
extracted `with_capacity` is related to it separately in the bridge (`with_capacity_rel`: the new
buffer satisfies `Inv` at capacity `max cap 1`).
`VecQueue`'s `VQ` has no such invariant and `VecQueue::with_capacity(0)` does not round, which is
the one recorded difference between the two queues.

The interface instance (`QueueModel`/`BoundedQueueLaws` on `BQ α := {r // r.Inv}`) is the
refinement certificate in the form the library retrieves: `RingBuffer` refines `BoundedQueue`.
-/
namespace FramedChannel

namespace RingBuffer

/-! ## Proof-ladder records for the shared-proof pair

`push_inv` and `pop_inv` are proved in `Model/RingBuffer/Defs.lean`, which the approved
specification imports, so their proofs are not wrapped in `rung` (that would change the approved
digests). They are recorded here, after the fact: the non-retrieval rungs are audited against
their statements, and the record says the retrieval audit did not run (see `Ladder.lean`). -/

ladder_record% push_inv manual
ladder_record% pop_inv manual

/-- Error agreement, success half. `[PROVED: kernel]` -/
theorem push_ok (α : Type) (r : RingBuffer α) (x : α) (h : ¬ r.full) :
    ∃ r', r.push x = .ok r' := by
  rung simp => simp_all [push, full]

/-- Error agreement, failure half. `[PROVED: kernel]` -/
theorem push_fail (α : Type) (r : RingBuffer α) (x : α) (h : r.full) : r.push x = .fail := by
  rung simp => simp_all [push, full]

/-- Invariant preservation, the automation probe: `grind` closes all four conjuncts at once given
`Nat.mod_add_mod` as a hypothesis. `[PROVED: kernel]` (adds `Classical.choice`). -/
theorem push_inv_grind (α : Type) (r : RingBuffer α) (x : α) (hInv : r.Inv) (h : ¬ r.full)
    (r' : RingBuffer α) (hpush : r.push x = .ok r') : r'.Inv := by
  simp only [full, beq_iff_eq] at h
  simp only [push, beq_iff_eq, h, ↓reduceIte, Result.ok.injEq] at hpush
  subst hpush
  simp only [Inv, List.length_set] at hInv ⊢
  have := Nat.mod_add_mod (r.head + r.len) r.buf.length 1
  grind

/-- The modular-index lemma: offsets `i < len < cap` from the same base never collide modulo
`cap`. The component's one non-automatic fact (the modulus is a variable, so `omega` alone cannot
close it), registered as a lemma node. `[PROVED: kernel]` -/
theorem idx_ne (head i len cap : Nat) (hi : i < len) (hlen : len < cap) :
    (head + i) % cap ≠ (head + len) % cap := by
  rung manual =>
    intro heq
    have := Nat.sub_mod_eq_zero_of_mod_eq heq.symm
    have hsub : head + len - (head + i) = len - i := by omega
    rw [hsub] at this
    have hlt : len - i < cap := by omega
    have hpos : 0 < len - i := by omega
    rw [Nat.mod_eq_of_lt hlt] at this
    omega

/-- Refinement: `push` commutes with the abstraction function. `[PROVED: kernel]` -/
theorem push_contents (α : Type) [Inhabited α] (r : RingBuffer α) (x : α) (hInv : r.Inv)
    (h : ¬ r.full) (r' : RingBuffer α) (hpush : r.push x = .ok r') :
    r'.contents = r.contents ++ [x] := by
  rung manual =>
    simp only [full, beq_iff_eq] at h
    simp only [push, beq_iff_eq, h, ↓reduceIte, Result.ok.injEq] at hpush
    subst hpush
    obtain ⟨h0, hlen, hhead, htail⟩ := hInv
    have hlt : r.len < r.buf.length := Nat.lt_of_le_of_ne hlen h
    simp only [contents, List.length_set, List.range_succ, List.map_append, List.map_cons,
      List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [htail]
      have hne := idx_ne r.head i r.len r.buf.length hi hlt
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]
    · rw [htail, List.getD_eq_getElem?_getD]
      have hin : (r.head + r.len) % r.buf.length < r.buf.length := Nat.mod_lt _ h0
      rw [List.getElem?_set_self hin]
      rfl

/-- The postcondition form an Aeneas `@[step]` spec lemma takes, derived from the three theorems
above. Aeneas's `⦃ ⦄` postcondition notation and its `@[step]` attribute live in a library not
available here, so the statement is spelled out as an existential. `[PROVED: kernel]` -/
theorem push_spec (α : Type) [Inhabited α] (r : RingBuffer α) (x : α) (hInv : r.Inv)
    (h : ¬ r.full) :
    ∃ r', r.push x = .ok r' ∧ r'.Inv ∧ r'.contents = r.contents ++ [x] := by
  rung manual =>
    obtain ⟨r', hr'⟩ := push_ok α r x h
    exact ⟨r', hr', push_inv α r x hInv h r' hr', push_contents α r x hInv h r' hr'⟩

/-- Bounds: `push` leaves the backing store's length unchanged and the occupancy within it, so a
successful push can never make the buffer describe more elements than it stores -- the Lean
counterpart of "no index in `rust/src/ring_buffer.rs` runs past the allocation".
`[PROVED: kernel]` -/
theorem push_bounded (α : Type) (r r' : RingBuffer α) (x : α) (hInv : r.Inv)
    (h : r.push x = .ok r') :
    r'.buf.length = r.buf.length ∧ r'.len ≤ r'.buf.length := by
  rung grind => grind [push, RingBuffer.Inv]

/-! ## Seed tactics: `inv_preserve` and `refine_commute`

Two macro tactics that replay the `push` proof scripts at `pop`, with `hygiene` off so the fixed
hypothesis names `h`, `hInv`, `r`, `x` of the obligation shape resolve; the step hypothesis is
passed as an argument (`hpush` or `hpop`). All four obligations close by them:

| Obligation      | Seed tactic      | Needed beyond the `push` script                           |
|-----------------|------------------|-----------------------------------------------------------|
| `push_inv`      | `inv_preserve`   | nothing                                                   |
| `pop_inv`       | `inv_preserve`   | `Nat.mod_lt` on conjunct 3, `congr 1; omega` on 4         |
| `push_contents` | `refine_commute` | nothing (first branch)                                    |
| `pop_contents`  | `refine_commute` | own branch: `List.range_succ_eq_map`, `List.map_map`      |

`pop_inv`'s proof is `inv_preserve hpop`; `push_inv_tac`, `push_contents_tac` and
`pop_contents_tac` at the end of the module replay the other three. `inv_preserve`'s first
conjunct-4 branch ends in `done` because `rw` can succeed without closing the goal, which would
otherwise commit to the wrong branch on `pop_inv`. -/

set_option hygiene false in
/-- Replays the refinement-commutation script. The `push` and `pop` skeletons differ after the
unfolding (append versus cons on `List.range`), so the macro carries one branch per shape. -/
macro "refine_commute" hstep:ident : tactic => `(tactic| (
  simp only [full, empty, beq_iff_eq] at h
  simp only [push, pop, beq_iff_eq, h, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at $hstep:ident
  first
    | subst $hstep:ident
    | (obtain ⟨rfl, $hstep:ident⟩ := $hstep:ident; subst $hstep:ident)
  obtain ⟨h0, hlen, hhead, htail⟩ := hInv
  first
    | (have hlt : r.len < r.buf.length := Nat.lt_of_le_of_ne hlen h
       simp only [contents, List.length_set, List.range_succ, List.map_append, List.map_cons,
         List.map_nil]
       congr 1
       · apply List.map_congr_left
         intro i hi
         simp only [List.mem_range] at hi
         rw [htail]
         have hne := idx_ne r.head i r.len r.buf.length hi hlt
         rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]
       · rw [htail, List.getD_eq_getElem?_getD]
         have hin : (r.head + r.len) % r.buf.length < r.buf.length := Nat.mod_lt _ h0
         rw [List.getElem?_set_self hin]
         rfl)
    | (obtain ⟨n, hn⟩ : ∃ n, r.len = n + 1 := ⟨r.len - 1, by omega⟩
       simp only [contents, hn, Nat.add_sub_cancel, List.range_succ_eq_map, List.map_cons,
         List.map_map]
       congr 1
       · rw [Nat.add_zero, Nat.mod_eq_of_lt hhead]
       · apply List.map_congr_left
         intro i _
         simp only [Function.comp, Nat.succ_eq_add_one]
         rw [Nat.mod_add_mod]
         have hi : r.head + (i + 1) = r.head + 1 + i := by omega
         rw [hi])))

/-! ## The second stamp: `pop` -/

/-- Error agreement, success half. `[PROVED: kernel]` -/
theorem pop_ok (α : Type) [Inhabited α] (r : RingBuffer α) (h : ¬ r.empty) :
    ∃ x r', r.pop = .ok (x, r') := by
  rung simp => simp_all [pop, empty]

/-- Error agreement, failure half. `[PROVED: kernel]` -/
theorem pop_fail (α : Type) [Inhabited α] (r : RingBuffer α) (h : r.empty) : r.pop = .fail := by
  rung simp => simp_all [pop, empty]

/-- Refinement for `pop`: the abstraction function sees the head element removed.
`[PROVED: kernel]` -/
theorem pop_contents (α : Type) [Inhabited α] (r : RingBuffer α) (hInv : r.Inv)
    (h : ¬ r.empty) (x : α) (r' : RingBuffer α) (hpop : r.pop = .ok (x, r')) :
    r.contents = x :: r'.contents := by
  rung manual =>
    simp only [empty, beq_iff_eq] at h
    simp only [pop, beq_iff_eq, h, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hpop
    obtain ⟨hx, hr'⟩ := hpop
    subst hx
    subst hr'
    obtain ⟨h0, hlen, hhead, htail⟩ := hInv
    obtain ⟨n, hn⟩ : ∃ n, r.len = n + 1 := ⟨r.len - 1, by omega⟩
    simp only [contents, hn, Nat.add_sub_cancel, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    · rw [Nat.add_zero, Nat.mod_eq_of_lt hhead]
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.succ_eq_add_one]
      rw [Nat.mod_add_mod]
      have hi : r.head + (i + 1) = r.head + 1 + i := by omega
      rw [hi]

/-- The `@[step]`-shaped postcondition for `pop`, derived from `pop_ok`, `pop_inv` and
`pop_contents`. `[PROVED: kernel]` -/
theorem pop_spec (α : Type) [Inhabited α] (r : RingBuffer α) (hInv : r.Inv) (h : ¬ r.empty) :
    ∃ x r', r.pop = .ok (x, r') ∧ r'.Inv ∧ r.contents = x :: r'.contents := by
  rung manual =>
    obtain ⟨x, r', hr'⟩ := pop_ok α r h
    exact ⟨x, r', hr', pop_inv α r hInv h x r' hr', pop_contents α r hInv h x r' hr'⟩

end RingBuffer

/-! ## The interface instance

`QueueModel` (L0) and `BoundedQueueLaws` (L1) are specification, declared in `Spec/Queue.lean`.
The instance below is stated on the invariant subtype `{r : RingBuffer α // r.Inv}`, because the
laws must hold on every value of the instance type and a raw `RingBuffer` violating `Inv` has
meaningless `contents`. -/

namespace RingBuffer

theorem pushBQ_ok {α : Type} [Inhabited α] (q : BQ α) (x : α) (h : ¬ q.1.full) :
    ∃ q', pushBQ q x = .ok q' ∧ q'.1.contents = q.1.contents ++ [x] := by
  unfold pushBQ
  rw [dif_neg h]
  split
  · rename_i r' hp
    exact ⟨_, rfl, push_contents α q.1 x q.2 h r' hp⟩
  · rename_i hp
    obtain ⟨r', hr'⟩ := push_ok α q.1 x h
    rw [hr'] at hp
    exact absurd hp (by simp)

theorem popBQ_ok {α : Type} [Inhabited α] (q : BQ α) (h : ¬ q.1.empty) :
    ∃ x q', popBQ q = .ok (x, q') ∧ q.1.contents = x :: q'.1.contents := by
  unfold popBQ
  rw [dif_neg h]
  split
  · rename_i x r' hp
    exact ⟨x, _, rfl, pop_contents α q.1 q.2 h x r' hp⟩
  · rename_i hp
    obtain ⟨x, r', hr'⟩ := pop_ok α q.1 h
    rw [hr'] at hp
    exact absurd hp (by simp)

/-- The refinement certificate as an interface instance: `RingBuffer` (on its invariant subtype)
is a `BoundedQueue`. `[PROVED: kernel]` -/
instance instBoundedQueueLaws (α : Type) [Inhabited α] : BoundedQueueLaws (BQ α) α where
  push_law := pushBQ_ok
  pop_law := popBQ_ok
  full_law q x h := by
    have h' : q.1.full = true := h
    show pushBQ q x = .fail
    unfold pushBQ
    rw [dif_pos h']
  empty_law q h := by
    have h' : q.1.empty = true := h
    show popBQ q = .fail
    unfold popBQ
    rw [dif_pos h']
  not_full_of_lt q h := by
    show ¬ q.1.full
    have hl : q.1.contents.length = q.1.len := by simp [contents]
    change q.1.contents.length < q.1.buf.length at h
    simp only [full, beq_iff_eq]
    omega
  push_capacity q x q' h := by
    change pushBQ q x = .ok q' at h
    show q'.1.buf.length = q.1.buf.length
    unfold pushBQ at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · rename_i r' hp
        simp only [Result.ok.injEq] at h
        subst h
        simp only [push] at hp
        split at hp
        · exact absurd hp (by simp)
        · simp only [Result.ok.injEq] at hp; subst hp; simp
      · exact absurd h (by simp)

ladder_record% instBoundedQueueLaws instance

/-- Reuse measurement: `push_inv` by the seed tactic. -/
theorem push_inv_tac (α : Type) (r : RingBuffer α) (x : α) (hInv : r.Inv) (h : ¬ r.full)
    (r' : RingBuffer α) (hpush : r.push x = .ok r') : r'.Inv := by
  inv_preserve hpush

/-- Reuse measurement: `push_contents` by the seed tactic. -/
theorem push_contents_tac (α : Type) [Inhabited α] (r : RingBuffer α) (x : α) (hInv : r.Inv)
    (h : ¬ r.full) (r' : RingBuffer α) (hpush : r.push x = .ok r') :
    r'.contents = r.contents ++ [x] := by
  refine_commute hpush

/-- Reuse measurement: `pop_contents` by the seed tactic. -/
theorem pop_contents_tac (α : Type) [Inhabited α] (r : RingBuffer α) (hInv : r.Inv)
    (h : ¬ r.empty) (x : α) (r' : RingBuffer α) (hpop : r.pop = .ok (x, r')) :
    r.contents = x :: r'.contents := by
  refine_commute hpop

#print axioms push_ok
#print axioms push_fail
#print axioms push_inv_grind
#print axioms idx_ne
#print axioms push_contents
#print axioms push_spec
#print axioms push_bounded
#print axioms pop_ok
#print axioms pop_fail
#print axioms pop_contents
#print axioms pop_spec
#print axioms instBoundedQueueLaws
#print axioms push_inv_tac
#print axioms push_contents_tac
#print axioms pop_contents_tac

end RingBuffer

end FramedChannel
