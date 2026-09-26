-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Instance
import FramedChannelAeneas.Bridge.Queue.Traits
import FramedChannelAeneas.Bridge.Channel.Abstraction
import FramedChannelAeneas.Bridge.StuffedChannel.Defs
import FramedChannel.Composition.StuffedChannel.Theorems

/-!
# Bridge/StuffedChannel/Abstraction: the extracted stuffed channel, read as the specification's

`[HAND-WRITTEN]` -- the abstraction the transparent channel's refinement theorems (`Frame.lean`,
`Refinement.lean`, `Composite.lean` and `Instance.lean` beside this file) are stated over.

## Two byte views

The specification `SChan` carries its wire as `List Nat`, because the composite is generic over a
`CodecModel C (List Nat)` and because `Bridge/Stuff/` already reads machine bytes that way
(`stuff.bytesOf`). Payload frames are still `List (BitVec 8)`, read through `crc8.bitsOf`, because
`Channel.Frame` is what the composite delivers and what the frame carrier
`Bridge.channel.instFrameCarrierVecU8` is stated at. `bytesOf_eq_map_toNat` and
`map_ofNat_bytesOf` are the two directions between the views; everything else about frames and
queues is `Bridge/Channel/Abstraction.lean`'s and is reused, not restated.

## The component tags

The extracted Rust calls `stuff::encode_frame`/`stuff::unstuff` and `crc8::crc8` directly, so this
bridge states the model side at the concrete component models: `C := Stuff.Hdlc`,
`K := Crc8.Bitwise`. `encode_hdlc`, `decode_hdlc` and `digest_bitwise` are the three spelling
identities that let a proof move between the interface projection and the model function; each is
`rfl`, not an obligation.

## The relation

`SChanRel c m` relates an extracted `stuffed_channel.StuffedChannel S` to a specification channel
whose queue is `Bridge/Queue/Instance.lean`'s extracted carrier `Ext S Q (Vec U8) inst R`: the same
extracted queue state, the same wire bytes, the same in-flight count. Because the model queue *is*
the extracted carrier, every composite theorem proved from the bounded-queue laws applies to it
through `QueueSim.boundedQueueLaws`, with no concrete queue named.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuffed_channel
open framed_channel
open FramedChannel.Bridge.stuff (bytesOf)
open FramedChannel.Bridge.crc8 (bitsOf)
open FramedChannel.Channel (Byte Frame FrameOK FrameCarrier lenBytes)

/-! ## The two byte views -/

/-- The stuffing bridge's byte abstraction is the CRC bridge's, read as naturals. -/
theorem bytesOf_eq_map_toNat (l : List Std.U8) : bytesOf l = (bitsOf l).map BitVec.toNat := by
  simp [bytesOf, bitsOf, List.map_map]

/-- And back: naturals below 256 read as the bit vectors they came from. -/
theorem map_ofNat_bytesOf (l : List Std.U8) : (bytesOf l).map (BitVec.ofNat 8) = bitsOf l := by
  rw [bytesOf_eq_map_toNat, FramedChannel.Channel.ofNat_toNat_map]

/-- The stuffing bridge's byte abstraction is the varint bridge's; the two are the same function in
two namespaces, and `Frame.lean` moves between them when it reuses `varint.decode_refines`. -/
theorem bytesOf_eq_varint_bytesOf (l : List Std.U8) :
    bytesOf l = FramedChannel.Bridge.varint.bytesOf l := rfl

/-- `bytesOf` on a cons. -/
theorem bytesOf_cons (x : Std.U8) (xs : List Std.U8) : bytesOf (x :: xs) = x.val :: bytesOf xs := rfl

/-! ## The component tags, as spellings -/

/-- The HDLC codec's `encode` projection is the model's `Stuff.encode`. -/
theorem encode_hdlc : CodecModel.encode (C := FramedChannel.Stuff.Hdlc) = FramedChannel.Stuff.encode :=
  rfl

/-- The HDLC codec's `decode` projection is the model's `Stuff.decode`. -/
theorem decode_hdlc : CodecModel.decode (C := FramedChannel.Stuff.Hdlc) = FramedChannel.Stuff.decode :=
  rfl

/-- The bitwise CRC-8's `digest` projection is the model's `crc8Bits`. -/
theorem digest_bitwise :
    ChecksumModel.digest (C := FramedChannel.Crc8.Bitwise) = FramedChannel.Crc8.crc8Bits := rfl

/-! ## The frame body and the stuffed wire, at the concrete components -/

/-- The frame body at the bitwise checksum, with its length prefix already read as a varint
encoding: the form every refinement in `Frame.lean` works against. -/
theorem body_eq (p : Frame) :
    FramedChannel.StuffedChannel.body (K := FramedChannel.Crc8.Bitwise) p
      = FramedChannel.Varint.encode p.length
        ++ (p ++ [FramedChannel.Crc8.crc8Bits p]).map BitVec.toNat := by
  simp only [FramedChannel.StuffedChannel.body, digest_bitwise, List.map_append,
    FramedChannel.Channel.toNat_lenBytes]

/-- The stuffed wire at the concrete components: the body, framed by HDLC stuffing. -/
theorem encodeStuffed_eq (p : Frame) :
    FramedChannel.StuffedChannel.encodeStuffed (C := FramedChannel.Stuff.Hdlc)
        (K := FramedChannel.Crc8.Bitwise) p
      = FramedChannel.Stuff.encode (FramedChannel.StuffedChannel.body
          (K := FramedChannel.Crc8.Bitwise) p) := rfl

/-- The body's length: the varint prefix, the payload, and the one check byte. -/
theorem body_length (p : Frame) :
    (FramedChannel.StuffedChannel.body (K := FramedChannel.Crc8.Bitwise) p).length
      = (FramedChannel.Varint.encode p.length).length + p.length + 1 := by
  rw [body_eq]
  simp only [List.length_append, List.length_map, List.length_singleton]
  omega

/-- A frame body is at most six bytes longer than its payload: at most five varint length bytes and
one check byte. This is what bounds the wire room `send` needs. -/
theorem body_length_le (p : Frame) (hp : FrameOK p) :
    (FramedChannel.StuffedChannel.body (K := FramedChannel.Crc8.Bitwise) p).length
      ≤ p.length + 6 := by
  have h := FramedChannel.Varint.encode_length_le p.length (by simpa [FrameOK] using hp)
  rw [body_length]
  omega

end FramedChannel.Bridge.stuffed_channel

#print axioms FramedChannel.Bridge.stuffed_channel.bytesOf_eq_map_toNat
#print axioms FramedChannel.Bridge.stuffed_channel.map_ofNat_bytesOf
#print axioms FramedChannel.Bridge.stuffed_channel.bytesOf_eq_varint_bytesOf
#print axioms FramedChannel.Bridge.stuffed_channel.bytesOf_cons
#print axioms FramedChannel.Bridge.stuffed_channel.encode_hdlc
#print axioms FramedChannel.Bridge.stuffed_channel.decode_hdlc
#print axioms FramedChannel.Bridge.stuffed_channel.digest_bitwise
#print axioms FramedChannel.Bridge.stuffed_channel.body_eq
#print axioms FramedChannel.Bridge.stuffed_channel.encodeStuffed_eq
#print axioms FramedChannel.Bridge.stuffed_channel.body_length
#print axioms FramedChannel.Bridge.stuffed_channel.body_length_le
