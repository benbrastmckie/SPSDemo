-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Instance
import FramedChannelAeneas.Bridge.Queue.Traits
import FramedChannelAeneas.Bridge.Channel.Defs
import FramedChannel.Composition.Channel.Theorems

/-!
# Bridge/Channel/Abstraction: the extracted channel, read as the specification channel

`[HAND-WRITTEN]` -- the abstraction the channel's refinement theorems (`Frame.lean`,
`Refinement.lean`, `Composite.lean` and `Instance.lean` beside this file) are stated over.

## Bytes

The specification channel (`lean/FramedChannel/Composition/Channel/Theorems.lean`) works over
`List (BitVec 8)`. The CRC-8 bridge already reads machine bytes that way (`crc8.bitsOf`), and the
varint bridge reads them as naturals (`varint.bytesOf`); `bitsOf_eq_bytesOf_map` connects the two,
so the channel uses `bitsOf` for the wire and for payloads.

## Frames as queue elements

Charon and Aeneas turn `Q: BoundedQueue<Frame>` into a record argument
`queue.BoundedQueue Q (alloc.vec.Vec Std.U8)`: the extracted queue holds machine vectors. The
specification channel `Chan` is generic over its element type through `FrameCarrier`, and
`instFrameCarrierVecU8` is the carrier at `alloc.vec.Vec Std.U8`: a frame becomes the vector of its
bytes. A frame longer than `Usize.max` has no vector, so the carrier maps it to the empty vector;
`frameOK_fits` shows that no frame the channel accepts is that long, and `ofFrame_val` and
`ofFrame_bitsOf` are the two directions of the correspondence on frames that fit.

## The relation

`ChanRel c m` relates an extracted `channel.Channel S` to a specification channel whose queue is
`Bridge/Queue/Instance.lean`'s extracted carrier `Ext S Q (Vec U8) inst R`: the same extracted
queue state, the same wire bytes, the same in-flight count. Because the model queue *is* the
extracted carrier, every channel theorem proved from the bounded-queue laws applies to it through
`QueueSim.boundedQueueLaws`, with no concrete queue named.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.channel
open framed_channel
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Frame Chan FrameCarrier FrameOK)

/-- The two byte abstractions agree: bit vectors are the natural values read at width 8. -/
theorem bitsOf_eq_bytesOf_map (l : List Std.U8) :
    bitsOf l = (FramedChannel.Bridge.varint.bytesOf l).map (BitVec.ofNat 8) := by
  simp [bitsOf, FramedChannel.Bridge.varint.bytesOf, List.map_map]

/-- A `u32` value always fits a `usize`, on both platforms Aeneas models. -/
theorem u32_max_le_usize_max : U32.max ≤ Usize.max := by scalar_tac

/-- A frame that fits reads back from its carrier vector. -/
theorem ofFrame_val (p : Frame) (h : p.length ≤ Usize.max) :
    bitsOf (FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) p).val = p := by
  show bitsOf (vecOfFrame p).val = p
  simp [vecOfFrame, h, bitsOf, List.map_map]

/-- A machine vector is the carrier of the frame it reads as. -/
theorem ofFrame_bitsOf (v : alloc.vec.Vec Std.U8) :
    FrameCarrier.ofFrame (E := alloc.vec.Vec Std.U8) (bitsOf v.val) = v := by
  show vecOfFrame (bitsOf v.val) = v
  have h : (bitsOf v.val).length ≤ Usize.max := by simp only [bitsOf, List.length_map]; scalar_tac
  unfold vecOfFrame
  rw [dif_pos h]
  apply alloc.vec.Vec.ext
  simp only [alloc.vec.Vec.from_val, bitsOf, List.map_map]
  conv => rhs; rw [← List.map_id v.val]
  rfl

/-- Every frame the channel accepts fits a vector. -/
theorem frameOK_fits (p : Frame) (h : FrameOK p) : p.length ≤ Usize.max := by
  simp only [FrameOK] at h
  scalar_tac

end FramedChannel.Bridge.channel

#print axioms FramedChannel.Bridge.channel.bitsOf_eq_bytesOf_map
#print axioms FramedChannel.Bridge.channel.u32_max_le_usize_max
#print axioms FramedChannel.Bridge.channel.ofFrame_val
#print axioms FramedChannel.Bridge.channel.ofFrame_bitsOf
#print axioms FramedChannel.Bridge.channel.frameOK_fits
