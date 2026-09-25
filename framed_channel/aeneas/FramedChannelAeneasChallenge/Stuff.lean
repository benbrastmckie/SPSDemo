-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Stuff.Defs

/-!
# FramedChannelAeneasChallenge.Stuff: approved statements (extracted HDLC byte-stuffing codec)

Statement-only restatements of the registered theorems; the proofs are in
`aeneas/FramedChannelAeneas/Bridge/Stuff/{Stuff,Unstuff,Instance}.lean`. See
`aeneas/FramedChannelAeneasChallenge.lean` for what a Challenge module is and what the gate checks.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuff
open framed_channel

/-- Stuffing refinement: the extracted `stuff` appends exactly the model's stuffed payload, and
never fails, given room for two bytes per input byte. -/
theorem stuff_refines (payload : Slice Std.U8) (out : alloc.vec.Vec Std.U8)
    (h : out.val.length + 2 * payload.val.length ≤ Usize.max) :
    stuff.stuff payload out
      ⦃ v => bytesOf v.val =
        bytesOf out.val ++ FramedChannel.Stuff.stuff (bytesOf payload.val) ⦄ := sorry

/-- Framing refinement: the extracted `encode_frame` appends exactly the model's `encode` -- the
stuffed payload followed by the terminating flag -- and never fails, given room for the flag as
well. -/
theorem encode_frame_refines (payload : Slice Std.U8) (out : alloc.vec.Vec Std.U8)
    (h : out.val.length + 2 * payload.val.length + 1 ≤ Usize.max) :
    stuff.encode_frame payload out
      ⦃ v => bytesOf v.val =
        bytesOf out.val ++ FramedChannel.Stuff.encode (bytesOf payload.val) ⦄ := sorry

/-- Success agreement: an extracted `Ok (out, k)` is a model success with the same payload and the
same residual bytes. -/
theorem decode_ok_refines (wire : Slice Std.U8) :
    stuff.unstuff wire ⦃ r => ∀ out k, r = .Ok (out, k) →
      FramedChannel.Stuff.decode (bytesOf wire.val)
        = .ok (bytesOf out.val, (bytesOf wire.val).drop k.val) ⦄ := sorry

/-- Completeness: a model success is an extracted `Ok` with the same payload, a consumed count
within the input, and the same residual bytes. -/
theorem decode_complete (wire : Slice Std.U8) (p rest : List Nat)
    (h : FramedChannel.Stuff.decode (bytesOf wire.val) = .ok (p, rest)) :
    stuff.unstuff wire ⦃ r => ∃ out k, r = .Ok (out, k) ∧ bytesOf out.val = p ∧
      k.val ≤ wire.val.length ∧ (bytesOf wire.val).drop k.val = rest ⦄ := sorry

/-- Error agreement: the extracted `unstuff` returns `Err` exactly when the model refuses. Unlike
the varint codec, whose `Overlong` rejection is stricter than its model, the two agree exactly here:
there is no input the Rust refuses and the model accepts, or the other way round. -/
theorem decode_err_iff (wire : Slice Std.U8) :
    stuff.unstuff wire ⦃ r => (∃ e, r = .Err e) ↔
      FramedChannel.Stuff.decode (bytesOf wire.val) = .fail ⦄ := sorry

/-- The extracted round trip: reading back what the extracted `encode_frame` wrote into an empty
vector returns exactly the payload, with every byte consumed. The one hypothesis is the same
`Vec::push` failure-freedom bound `encode_frame_refines` carries. -/
theorem roundtrip_extracted (payload : Slice Std.U8)
    (h : 2 * payload.val.length + 1 ≤ Usize.max) :
    stuff.encode_frame payload (alloc.vec.Vec.new Std.U8) ⦃ v =>
      stuff.unstuff (alloc.vec.Vec.deref v) ⦃ r => ∃ out k, r = .Ok (out, k) ∧
        bytesOf out.val = bytesOf payload.val ∧ k.val = v.val.length ⦄ ⦄ := sorry

/-- The codec laws on the extracted stuffing codec. -/
theorem instCodecLaws_extracted : CodecLaws ExtractedHdlc (List Nat) := sorry

end FramedChannel.Bridge.stuff
