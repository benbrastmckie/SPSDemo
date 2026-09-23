-- SPDX-License-Identifier: Apache-2.0
-- A dishonest label: the shipped two-step script of `push_fail` labelled manual. The audit's
-- canonical simp attempt closes the goal, so the build must fail naming the simp rung.
import FramedChannel.Ladder
import FramedChannel.Model.RingBuffer.Defs

namespace FramedChannel.RingBuffer

theorem push_fail (α : Type) (r : RingBuffer α) (x : α) (h : r.full) : r.push x = .fail := by
  rung manual =>
    simp only [full, beq_iff_eq] at h
    simp [push, h]

end FramedChannel.RingBuffer
