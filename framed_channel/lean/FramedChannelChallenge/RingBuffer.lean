-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Model.RingBuffer.Defs

/-!
# FramedChannelChallenge.RingBuffer: approved statements (ring buffer model)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Model/RingBuffer/Theorems.lean`. See `lean/FramedChannelChallenge.lean` for what a
Challenge module is and what the gate checks. `push_inv` and `pop_inv` are not restated: `pushBQ`
and `popBQ` are built from them, so they are imported proved from `Model/RingBuffer/Defs.lean` (the
`shared-proof` rows of `certificate/policy.txt`).
-/

namespace FramedChannel
namespace RingBuffer

/-- Error agreement, success half. -/
theorem push_ok (α : Type) (r : RingBuffer α) (x : α) (h : ¬ r.full) :
    ∃ r', r.push x = .ok r' := sorry

/-- Error agreement, failure half. -/
theorem push_fail (α : Type) (r : RingBuffer α) (x : α) (h : r.full) : r.push x = .fail := sorry

/-- The modular-index lemma: offsets `i < len < cap` from the same base never collide modulo
`cap`. The component's one non-automatic fact, registered as a lemma node. -/
theorem idx_ne (head i len cap : Nat) (hi : i < len) (hlen : len < cap) :
    (head + i) % cap ≠ (head + len) % cap := sorry

/-- Refinement: `push` commutes with the abstraction function. -/
theorem push_contents (α : Type) [Inhabited α] (r : RingBuffer α) (x : α) (hInv : r.Inv)
    (h : ¬ r.full) (r' : RingBuffer α) (hpush : r.push x = .ok r') :
    r'.contents = r.contents ++ [x] := sorry

/-- The postcondition form an Aeneas `@[step]` spec lemma takes, derived from the three theorems
above. Aeneas's `⦃ ⦄` postcondition notation and its `@[step]` attribute live in a library not
available here, so the statement is spelled out as an existential. -/
theorem push_spec (α : Type) [Inhabited α] (r : RingBuffer α) (x : α) (hInv : r.Inv)
    (h : ¬ r.full) :
    ∃ r', r.push x = .ok r' ∧ r'.Inv ∧ r'.contents = r.contents ++ [x] := sorry

/-- Bounds: `push` leaves the backing store's length unchanged and the occupancy within it, so a
successful push can never make the buffer describe more elements than it stores -- the Lean
counterpart of "no index in `rust/src/ring_buffer.rs` runs past the allocation". -/
theorem push_bounded (α : Type) (r r' : RingBuffer α) (x : α) (hInv : r.Inv)
    (h : r.push x = .ok r') :
    r'.buf.length = r.buf.length ∧ r'.len ≤ r'.buf.length := sorry

/-- Error agreement, success half. -/
theorem pop_ok (α : Type) [Inhabited α] (r : RingBuffer α) (h : ¬ r.empty) :
    ∃ x r', r.pop = .ok (x, r') := sorry

/-- Error agreement, failure half. -/
theorem pop_fail (α : Type) [Inhabited α] (r : RingBuffer α) (h : r.empty) : r.pop = .fail := sorry

/-- Refinement for `pop`: the abstraction function sees the head element removed. -/
theorem pop_contents (α : Type) [Inhabited α] (r : RingBuffer α) (hInv : r.Inv)
    (h : ¬ r.empty) (x : α) (r' : RingBuffer α) (hpop : r.pop = .ok (x, r')) :
    r.contents = x :: r'.contents := sorry

/-- The `@[step]`-shaped postcondition for `pop`, derived from `pop_ok`, `pop_inv` and
`pop_contents`. -/
theorem pop_spec (α : Type) [Inhabited α] (r : RingBuffer α) (hInv : r.Inv) (h : ¬ r.empty) :
    ∃ x r', r.pop = .ok (x, r') ∧ r'.Inv ∧ r.contents = x :: r'.contents := sorry

/-- The refinement certificate as an interface instance: `RingBuffer` (on its invariant subtype)
is a `BoundedQueue`. -/
instance instBoundedQueueLaws (α : Type) [Inhabited α] : BoundedQueueLaws (BQ α) α := sorry
end RingBuffer
end FramedChannel
