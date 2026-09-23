-- SPDX-License-Identifier: Apache-2.0
-- An honest refutation record: the false theorem states exactly the negation of the candidate,
-- and the witness is read off the kernel-checked search theorem, never typed by hand.
import FramedChannel.Ladder

namespace FramedChannel

def small_candidate : Prop := ∀ n : Nat, n < 5

theorem search_small : (List.range 10).find? (fun n => !decide (n < 5)) = some 5 := by
  decide

theorem small_candidate_false : ¬ small_candidate := fun h => absurd (h 5) (by decide)

refuted% small_candidate small_candidate_false search_small

end FramedChannel
