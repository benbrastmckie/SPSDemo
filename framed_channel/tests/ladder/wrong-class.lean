-- SPDX-License-Identifier: Apache-2.0
-- A label that does not match its script: `simp` on a `grind` call.
import FramedChannel.Ladder
import FramedChannel.Model.RingBuffer.Defs

namespace FramedChannel.RingBuffer

theorem push_fail (α : Type) (r : RingBuffer α) (x : α) (h : r.full) : r.push x = .fail := by
  rung simp => grind [push, full]

end FramedChannel.RingBuffer
