-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Stuff.Unstuff

/-!
# Bridge/Stuff/Instance: the extracted stuffing codec satisfies `CodecLaws`

`[EXTRACTED: aeneas + bridge]` -- the codec row, stated about the Rust as extracted.

## Instantiated directly, with no simulation structure

Step 9.5 of `framed_channel/docs/adding-a-unit.md` asks a two-part question before a simulation
structure is owed: does the Rust dispatch through a trait, **and** is a composite proved generic over
it? For `stuff` the answer is no on both counts -- `stuff`, `encode_frame` and `unstuff` are free
functions and no composite is generic over them -- so `ExtractedHdlc` is given its `CodecModel`
instance directly in `Defs.lean` and the laws are derived here, exactly as `Varint` and `Crc8` do.
No `CodecSim` is built.

## How the laws are discharged

`extEncode_eq` is the load-bearing step: on the claimed domain the extracted `encode_frame`, run on
an empty vector and read back through `bytesOf`, produces *literally the model's* `encode`. Both laws
then reduce to model facts -- `stuff_roundtrip` and `encode_length_le` -- rather than being reproved
over machine values.

`Dom` repeats the model's domain (`Defs.lean`), and both conjuncts are used: the byte-range condition
to show the round trip through `sliceOfBytes` is lossless, and the length bound to keep the encoding
inside `maxLen` and inside `usize`.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.stuff
open framed_channel

/-- Re-slicing a list of bytes and abstracting it back is the identity: the modulo in
`sliceOfBytes` only bites on values of 256 or more, which the domain excludes. -/
theorem bytesOf_sliceOfBytes (bs : List Nat) (h : bs.length ≤ Usize.max) (hb : ∀ b ∈ bs, b < 256) :
    bytesOf (sliceOfBytes bs h).val = bs := by
  simp only [bytesOf, sliceOfBytes, Slice.from_val, List.map_map]
  refine (List.map_congr_left (fun x hx => ?_)).trans (List.map_id _)
  simp only [Function.comp_apply, id_eq, Std.UScalar.ofNatCore_val_eq]
  exact Nat.mod_eq_of_lt (hb x hx)

theorem sliceOfBytes_length (bs : List Nat) (h : bs.length ≤ Usize.max) :
    (sliceOfBytes bs h).val.length = bs.length := by simp [sliceOfBytes]

/-- The framed encoding stays inside the byte range: the stuffed payload does (the model's
`stuff_bytes_lt`) and the terminating flag does. -/
theorem encode_bytes_lt (p : List Nat) (hb : ∀ b ∈ p, b < 256) :
    ∀ b ∈ FramedChannel.Stuff.encode p, b < 256 := by
  intro b hbm
  rw [FramedChannel.Stuff.encode, List.mem_append] at hbm
  rcases hbm with h | h
  · exact FramedChannel.Stuff.stuff_bytes_lt p hb b h
  · simp only [List.mem_singleton] at h
    subst h
    decide

/-- On the claimed domain the extracted `encode_frame` produces exactly the model's `encode`. -/
theorem extEncode_eq (p : List Nat) (hb : ∀ b ∈ p, b < 256) (hl : p.length ≤ 255) :
    extEncode p = FramedChannel.Stuff.encode p := by
  have hu : p.length ≤ Usize.max := by scalar_tac
  have hcond : p.length ≤ Usize.max ∧ ∀ b ∈ p, b < 256 := ⟨hu, hb⟩
  have hsl : bytesOf (sliceOfBytes p hu).val = p := bytesOf_sliceOfBytes p hu hb
  have hbound : (alloc.vec.Vec.new Std.U8).val.length
      + 2 * (sliceOfBytes p hu).val.length + 1 ≤ Usize.max := by
    simp [sliceOfBytes]
    scalar_tac
  obtain ⟨v, hv, hbytes⟩ := (WP.spec_equiv_exists _ _).mp
    (encode_frame_refines (sliceOfBytes p hu) (alloc.vec.Vec.new Std.U8) hbound)
  unfold extEncode
  rw [dif_pos hcond]
  simp only [hv, Result.match.ok]
  rw [hbytes, hsl]
  simp [bytesOf, alloc.vec.Vec.new]

/-- The codec laws on the extracted stuffing codec. `[EXTRACTED: aeneas + bridge]` -/
theorem instCodecLaws_extracted : CodecLaws ExtractedHdlc (List Nat) where
  round_trip p hp := by
    obtain ⟨hb, hl⟩ := hp
    have henc : CodecModel.encode (C := ExtractedHdlc) p = FramedChannel.Stuff.encode p := by
      show extEncode p = _
      exact extEncode_eq p hb hl
    show extDecode (CodecModel.encode (C := ExtractedHdlc) p) = _
    rw [henc]
    have hlen : (FramedChannel.Stuff.encode p).length ≤ Usize.max := by
      have := FramedChannel.Stuff.encode_length_le p
      have : (FramedChannel.Stuff.encode p).length ≤ 511 := by omega
      scalar_tac
    have hbytes := encode_bytes_lt p hb
    have hcond : (FramedChannel.Stuff.encode p).length ≤ Usize.max ∧
        ∀ b ∈ FramedChannel.Stuff.encode p, b < 256 := ⟨hlen, hbytes⟩
    have hsl : bytesOf (sliceOfBytes (FramedChannel.Stuff.encode p) hlen).val
        = FramedChannel.Stuff.encode p :=
      bytesOf_sliceOfBytes _ hlen hbytes
    obtain ⟨r, hr, hpost⟩ := (WP.spec_equiv_exists _ _).mp
      (decode_complete (sliceOfBytes (FramedChannel.Stuff.encode p) hlen) p []
        (by rw [hsl]; exact FramedChannel.Stuff.stuff_roundtrip p))
    obtain ⟨out, k, rfl, hout, hk, hdrop⟩ := hpost
    unfold extDecode
    rw [dif_pos hcond]
    simp only [hr, Result.match.ok]
    rw [hsl] at hdrop
    rw [hout, hdrop]
  length_le p hp := by
    obtain ⟨hb, hl⟩ := hp
    show (extEncode p).length ≤ 2 * 255 + 1
    rw [extEncode_eq p hb hl]
    have := FramedChannel.Stuff.encode_length_le p
    omega

end FramedChannel.Bridge.stuff

#print axioms FramedChannel.Bridge.stuff.sliceOfBytes_length
#print axioms FramedChannel.Bridge.stuff.bytesOf_sliceOfBytes
#print axioms FramedChannel.Bridge.stuff.encode_bytes_lt
#print axioms FramedChannel.Bridge.stuff.extEncode_eq
#print axioms FramedChannel.Bridge.stuff.instCodecLaws_extracted
