-- SPDX-License-Identifier: Apache-2.0
-- An honest label: `push_fail`'s shape, closed by one simp call naming only definitions.
import FramedChannel.Ladder
import FramedChannel.Model.RingBuffer.Defs

namespace FramedChannel.RingBuffer

theorem push_fail (α : Type) (r : RingBuffer α) (x : α) (h : r.full) : r.push x = .fail := by
  rung simp => simp_all [push, full]

end FramedChannel.RingBuffer
