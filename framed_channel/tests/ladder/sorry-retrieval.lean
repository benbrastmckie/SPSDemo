-- SPDX-License-Identifier: Apache-2.0
-- A goal no rung closes (`idx_ne`: a variable modulus, outside omega and grind). The retrieval
-- attempt (`exact?`) and the others fail; none may be counted as closing through a `sorry`, and
-- nothing of theirs may leak: the record is manual and the declaration carries no sorry.
import FramedChannel.Ladder
import FramedChannel.Model.RingBuffer.Defs

namespace FramedChannel.RingBuffer

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

#print axioms idx_ne

end FramedChannel.RingBuffer
