-- SPDX-License-Identifier: Apache-2.0
-- A dishonest label one rung up: a restatement of a theorem the imports already prove
-- (`RingBuffer.push_inv`, in the definitions module), labelled manual. The audit runs where the
-- declaration is elaborated, where `exact?` finds the imported theorem, so the build must fail
-- naming the retrieval rung.
import FramedChannel.Ladder
import FramedChannel.Model.RingBuffer.Defs

namespace FramedChannel.RingBuffer

theorem push_inv_again (α : Type) (r : RingBuffer α) (x : α) (hInv : r.Inv) (h : ¬ r.full)
    (r' : RingBuffer α) (hpush : r.push x = .ok r') : r'.Inv := by
  rung manual =>
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

end FramedChannel.RingBuffer
