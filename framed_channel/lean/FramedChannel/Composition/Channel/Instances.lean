-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Composition.Channel.Theorems
import FramedChannel.Model.RingBuffer.Theorems
import FramedChannel.Model.VecQueue.Theorems

/-!
# Composition/Channel/Instances: substitution, the same theorem at two instances

`Composition/Channel/Theorems.lean` proves `deliver_spec` once, from the bounded-queue laws alone, and
imports no queue model. This module is where the composition layer meets the model layer: it
instantiates that one proof at the ring buffer (`RingBuffer.BQ`) and at the list-backed queue
(`VecQueue.VQ`) with no reproof. That is the substitution row `Channel[VQ/BQ]`. The
declarations are in namespace `FramedChannel.Channel`, beside the theorem they instantiate.
-/

namespace FramedChannel.Channel

open FramedChannel

/-- `deliver_spec` at the ring buffer. `[PROVED: kernel]` -/
theorem deliver_spec_RB (c : Chan (RingBuffer.BQ Frame)) (p : Frame) (ps : List Frame)
    (h : ChanInv (E := Frame) c (p :: ps)) :
    ∃ c', deliver (E := Frame) c = .ok c' ∧ c'.out.1.contents = c.out.1.contents ++ [p] ∧ ChanInv (E := Frame) c' ps := by
  rung retrieval => exact deliver_spec (RingBuffer.BQ Frame) Frame c p ps h

/-- `deliver_spec` at the list-backed queue, with no reproof. `[PROVED: kernel]` -/
theorem deliver_spec_VQ (c : Chan (VecQueue.VQ Frame)) (p : Frame) (ps : List Frame)
    (h : ChanInv (E := Frame) c (p :: ps)) :
    ∃ c', deliver (E := Frame) c = .ok c' ∧ c'.out.items = c.out.items ++ [p] ∧ ChanInv (E := Frame) c' ps := by
  rung retrieval => exact deliver_spec (VecQueue.VQ Frame) Frame c p ps h

#print axioms deliver_spec_RB
#print axioms deliver_spec_VQ

end FramedChannel.Channel
