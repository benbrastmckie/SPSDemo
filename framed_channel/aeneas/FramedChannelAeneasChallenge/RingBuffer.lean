-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.RingBuffer.Defs

/-!
# FramedChannelAeneasChallenge.RingBuffer: approved statements (extracted ring buffer)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/RingBuffer/{Refinement,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.ring_buffer
open framed_channel
variable {α : Type}

theorem push_full (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) (x : α) (h : (toModel r).full) :
    ring_buffer.RingBuffer.push dflt cln r x ⦃ p => p = (.Err (), r) ⦄ := sorry

theorem push_refines (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) (x : α) (hInv : (toModel r).Inv) (h : ¬ (toModel r).full) :
    ring_buffer.RingBuffer.push dflt cln r x
      ⦃ p => p.1 = .Ok () ∧ (toModel r).push x = .ok (toModel p.2) ⦄ := sorry

theorem pop_empty (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) (h : (toModel r).empty) :
    ring_buffer.RingBuffer.pop dflt cln r ⦃ p => p = (none, r) ⦄ := sorry

theorem pop_refines [Inhabited α] (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (hcln : CloneIsId cln) (r : ring_buffer.RingBuffer α)
    (hInv : (toModel r).Inv) (h : ¬ (toModel r).empty) :
    ring_buffer.RingBuffer.pop dflt cln r
      ⦃ p => ∃ y, p.1 = some y ∧ (toModel r).pop = .ok (y, toModel p.2) ⦄ := sorry

theorem capacity_agrees (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) :
    ring_buffer.RingBuffer.capacity dflt cln r ⦃ c => c.val = (toModel r).buf.length ⦄ := sorry

/-- The extracted `len` is the model's item count. -/
theorem len_agrees (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) :
    ring_buffer.RingBuffer.impl.len dflt cln r ⦃ n => n.val = (toModel r).len ⦄ := sorry

theorem is_full_agrees (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) :
    ring_buffer.RingBuffer.is_full dflt cln r ⦃ b => b = (toModel r).full ⦄ := sorry

theorem is_empty_agrees (dflt : core.default.Default α) (cln : core.clone.Clone α)
    (r : ring_buffer.RingBuffer α) :
    ring_buffer.RingBuffer.is_empty dflt cln r ⦃ b => b = (toModel r).empty ⦄ := sorry

/-- The extracted `BoundedQueue` record instance of the ring buffer simulates the model's
invariant subtype `BQ`, related by `toModel s = q.1`: the per-component input to every generic
transport theorem in `Bridge/Queue/Transport.lean`. -/
theorem sim {α : Type} [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) (hcln : CloneIsId cln) :
    QueueSim (ring_buffer.RingBuffer α) (FramedChannel.RingBuffer.BQ α) α
      (ring_buffer.RingBuffer.Insts.Framed_channelQueueBoundedQueue dflt cln)
      (fun s q => toModel s = q.1) := sorry

/-- `push_law` for the extracted code, derived from the generic transport: the extracted `push`
preserves `Inv` and appends to `contents`. -/
theorem push_law_extracted [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) (r : ring_buffer.RingBuffer α) (x : α)
    (hInv : (toModel r).Inv) (h : ¬ (toModel r).full) :
    ring_buffer.RingBuffer.push dflt cln r x
      ⦃ p => p.1 = .Ok () ∧ (toModel p.2).Inv ∧
        (toModel p.2).contents = (toModel r).contents ++ [x] ⦄ := sorry

/-- `pop_law` for the extracted code, derived from the generic transport: the extracted `pop`
preserves `Inv` and removes the front of `contents`. -/
theorem pop_law_extracted [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) (hcln : CloneIsId cln) (r : ring_buffer.RingBuffer α)
    (hInv : (toModel r).Inv) (h : ¬ (toModel r).empty) :
    ring_buffer.RingBuffer.pop dflt cln r
      ⦃ p => ∃ y, p.1 = some y ∧ (toModel p.2).Inv ∧
        (toModel r).contents = y :: (toModel p.2).contents ⦄ := sorry
end FramedChannel.Bridge.ring_buffer

open Aeneas Aeneas.Std Result
namespace FramedChannel.Bridge.ring_buffer
open framed_channel
variable {α : Type}

/-- The extracted ring buffer satisfies all six bounded-queue laws, on its own extracted carrier,
for any `Default` record and any `Clone` record with `CloneIsId`. -/
theorem instBoundedQueueLaws_extracted [Inhabited α] (dflt : core.default.Default α)
    (cln : core.clone.Clone α) (hcln : CloneIsId cln) :
    BoundedQueueLaws (ExtractedRB α dflt cln) α := sorry
end FramedChannel.Bridge.ring_buffer
