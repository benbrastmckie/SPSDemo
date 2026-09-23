-- SPDX-License-Identifier: Apache-2.0
-- A dishonest refutation record: the false theorem refutes a different candidate than the one
-- recorded. The command must fail.
import FramedChannel.Ladder

namespace FramedChannel

def small_candidate : Prop := ∀ n : Nat, n < 5

def other_candidate : Prop := ∀ n : Nat, n < 3

theorem search_small : (List.range 10).find? (fun n => !decide (n < 5)) = some 5 := by
  decide

theorem other_candidate_false : ¬ other_candidate := fun h => absurd (h 3) (by decide)

refuted% small_candidate other_candidate_false search_small

end FramedChannel
