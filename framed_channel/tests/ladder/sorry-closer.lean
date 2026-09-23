-- SPDX-License-Identifier: Apache-2.0
-- A goal whose canonical attempts "close" it only with a term carrying the `sorry` already in the
-- statement (`x = x ∨ sorry`). A closing attempt counts only when its term is free of
-- `sorry`, so the audit must not report simp; the record is manual. The declaration itself still
-- uses `sorry`, which Lean reports and the gate's sorry scan fails -- this fixture exercises only
-- the audit's sorry filter.
import FramedChannel.Ladder

namespace FramedChannel

theorem sorry_goal : ∀ x : Nat, x = x ∨ (sorry : Prop) := by
  rung manual => exact fun _ => Or.inl rfl

end FramedChannel
