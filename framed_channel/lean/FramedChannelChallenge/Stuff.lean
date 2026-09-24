-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Model.Stuff.Defs

/-!
# FramedChannelChallenge.Stuff: approved statements (HDLC byte-stuffing codec model)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Model/Stuff/Theorems.lean`. See `lean/FramedChannelChallenge.lean` for what a Challenge
module is and what the gate checks.
-/

namespace FramedChannel.Stuff

/-- The marker-free encoding invariant: a stuffed payload contains no frame boundary byte. This is
what makes `unstuff`'s scan-to-flag unambiguous and what the round trip below rests on. -/
theorem stuff_marker_free (p : List Nat) : ∀ c ∈ stuff p, c ≠ marker := sorry

/-- The round-trip law (the `D ∘ E = id` row): every payload decodes to itself with nothing left
over. Unlike `Varint.varint_roundtrip` this needs no domain hypothesis -- stuffing round-trips at
every payload, bounded or not. -/
theorem stuff_roundtrip (p : List Nat) : decode (encode p) = .ok (p, []) := sorry

/-- Bounds: stuffing at most doubles the payload, since the worst case emits two bytes per input
byte. This is the unit's real bounds row: it is unconditional and input-relative, so it is
strictly more informative than the constant `CodecLaws.length_le` demands. -/
theorem stuff_length_le (p : List Nat) : (stuff p).length ≤ 2 * p.length := sorry

/-- Bounds on the whole frame: the stuffed payload plus the one terminating flag byte. This is
what discharges `CodecLaws.length_le` on the claimed domain; without the domain's
`p.length ≤ 255`, the constant bound `maxLen` asks for is false, and
`Evidence/Countermodels.lean` refutes it in the kernel. -/
theorem encode_length_le (p : List Nat) : (encode p).length ≤ 2 * p.length + 1 := sorry

/-- The refinement certificate as an interface instance: the HDLC stuffing codec satisfies the
codec laws. `round_trip` discharges from `stuff_roundtrip`, which needs no hypothesis at all;
`length_le` from `encode_length_le` together with the domain's payload-length bound. -/
instance instCodecLaws : CodecLaws Hdlc (List Nat) := sorry

end FramedChannel.Stuff
