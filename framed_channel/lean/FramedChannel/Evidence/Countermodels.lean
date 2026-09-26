-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Model.Varint.Theorems
import FramedChannel.Model.Zigzag.Theorems
import FramedChannel.Model.SeqNum.Theorems
import FramedChannel.Model.Stuff.Theorems
import FramedChannel.Composition.Channel.Theorems

/-!
# Evidence/Countermodels: rejected candidate statements, refuted in the kernel

The last rung of the Prove step is the countermodel. A candidate statement that looks right but
is false is part of the evidence: it records why a registered theorem carries the hypothesis it
does, or why a design choice was made, and the refutation is checked like any proof.

Each candidate below has three parts, recorded together by `refuted%` (`Ladder.lean`):

* `<candidate> : Prop`, the rejected statement, as a named definition;
* `search_<...>`, a theorem that an explicit, finite enumeration's **first** failure is `w`,
  proved by `decide +kernel` -- so the kernel both runs the search and checks its result, and the
  witness is the first counterexample in the enumerated domain, not merely some counterexample;
* `<candidate>_false : ¬ <candidate>`, the refutation at that witness, also in the kernel.

`refuted%` checks that the false theorem states exactly `¬ <candidate>` and reads the witness off
the search theorem's right-hand side, so no witness is typed by hand into the record; `check.sh`
collects the `countermodel <candidate> <witness>` lines into `certificate/countermodels.txt`.

## What this module is not

**Nothing imports it** (a `check.sh` layer rule), and nothing here is registered or restated in
`FramedChannelChallenge/`: countermodels are evidence, not scored obligations, so they never
enter the bank, a manifest's `proofs:`, or an approval. Every declaration is kernel-only: no
`bv_decide`, no `native_decide`, no compiler-trusting axiom (the gate checks the axiom records).

The search is plain kernel evaluation over an enumeration chosen by hand (powers of two, payload
lengths `0..129`, small index triples). It is not a property-testing tool: it finds a
counterexample only inside the domain it is given. Plausible, which would generate inputs, is not
used: it is reachable only under `aeneas/` (a Mathlib dependency), and adding it to this core
package would need a `require` and a network fetch.
-/

namespace FramedChannel

open Channel

/-! ## 1. `encode_length_le` without its `n < 2 ^ 32` hypothesis -/

/-- The rejected candidate: every natural number encodes in at most five bytes. -/
def encode_length_le_unbounded : Prop := ∀ n : Nat, (Varint.encode n).length ≤ 5

/-- Over the powers of two below `2 ^ 64`, the first whose encoding is longer than five bytes is
`2 ^ 35` (`= 128 ^ 5`, where `encodeF 5` emits a sixth byte). `[PROVED: kernel]` -/
theorem search_encode_length_le_unbounded :
    ((List.range 64).map (2 ^ ·)).find? (fun n => !decide ((Varint.encode n).length ≤ 5))
      = some (2 ^ 35) := by
  decide +kernel

/-- `[PROVED: kernel]` -/
theorem encode_length_le_unbounded_false : ¬ encode_length_le_unbounded :=
  fun h => absurd (h (2 ^ 35)) (by decide +kernel)

refuted% encode_length_le_unbounded encode_length_le_unbounded_false search_encode_length_le_unbounded

/-! ## 2. `varint_roundtrip` without its `n < 2 ^ 32` hypothesis -/

/-- The rejected candidate: every natural number round-trips through the five-group codec. -/
def varint_roundtrip_unbounded : Prop := ∀ n : Nat, Varint.decode (Varint.encode n) = .ok (n, [])

/-- Over the powers of two below `2 ^ 64`, the first that does not round-trip is `2 ^ 35`: the
sixth byte is left over. `[PROVED: kernel]` -/
theorem search_varint_roundtrip_unbounded :
    ((List.range 64).map (2 ^ ·)).find?
        (fun n => !decide (Varint.decode (Varint.encode n) = .ok (n, [])))
      = some (2 ^ 35) := by
  decide +kernel

/-- `[PROVED: kernel]` -/
theorem varint_roundtrip_unbounded_false : ¬ varint_roundtrip_unbounded :=
  fun h => absurd (h (2 ^ 35)) (by decide +kernel)

refuted% varint_roundtrip_unbounded varint_roundtrip_unbounded_false search_varint_roundtrip_unbounded

/-! ## 3. A receiver that treats a second `0x7E` as a new frame boundary -/

/-- A candidate receiver that resynchronizes on a repeated marker: when the byte after a marker is
itself `0x7E`, it treats that byte as the start of the frame. This is the design `parseFrame`
deliberately does not have (see `Composition/Channel/Defs.lean`'s "Receiver model"). -/
def parseFrameResync : List Byte → Result (Frame × List Byte)
  | m :: b :: rest => if m = marker ∧ b = marker then parseFrame (b :: rest)
                      else parseFrame (m :: b :: rest)
  | bs => parseFrame bs

/-- The rejected candidate: the resynchronizing receiver round-trips every deliverable frame. -/
def parseFrameResync_roundtrip : Prop :=
  ∀ p : Frame, FrameOK p → parseFrameResync (encodeFrame p) = .ok (p, [])

set_option maxRecDepth 100000 in
/-- Over zero payloads of length `0..129`, the first the resynchronizing receiver fails to read
back is length `126`: its single varint length byte is `0x7E`. `[PROVED: kernel]` -/
theorem search_parseFrameResync_roundtrip :
    ((List.range 130).find? fun k => !decide
      (parseFrameResync (encodeFrame (List.replicate k 0#8)) = .ok (List.replicate k 0#8, [])))
      = some 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `FrameOK` has no `Decidable` instance, so it is unfolded before `decide`. `[PROVED: kernel]` -/
theorem parseFrameResync_roundtrip_false : ¬ parseFrameResync_roundtrip :=
  fun h => absurd (h (List.replicate 126 0#8) (by unfold FrameOK; decide +kernel))
    (by decide +kernel)

refuted% parseFrameResync_roundtrip parseFrameResync_roundtrip_false search_parseFrameResync_roundtrip

/-! ## 4. `RingBuffer.idx_ne` with `i ≤ len` in place of `i < len` -/

/-- The rejected candidate: the modular-index lemma with its strict hypothesis weakened. -/
def idx_ne_le : Prop :=
  ∀ head i len cap : Nat, i ≤ len → len < cap → (head + i) % cap ≠ (head + len) % cap

/-- Over `i, len < 3` at capacity `3` and head `0`, the first pair satisfying the weakened
hypotheses whose indices collide is `(0, 0)`: `i = len`. `[PROVED: kernel]` -/
theorem search_idx_ne_le :
    (((List.range 3).flatMap fun i => (List.range 3).map fun len => (i, len)).find?
        fun (i, len) => decide (i ≤ len ∧ len < 3 ∧ (0 + i) % 3 = (0 + len) % 3))
      = some (0, 0) := by
  decide +kernel

/-- `[PROVED: kernel]` -/
theorem idx_ne_le_false : ¬ idx_ne_le :=
  fun h => h 0 0 0 3 (Nat.le_refl 0) (by decide) rfl

refuted% idx_ne_le idx_ne_le_false search_idx_ne_le

/-! ## 5. Byte stuffing without expansion -/

/-- The rejected candidate: framing a payload costs at most the one flag byte -- that is, stuffing
never expands. It is the shape someone reaches for when writing the bound before noticing that an
escape emits two bytes for one. -/
def encode_no_expansion : Prop := ∀ p : List Nat, (Stuff.encode p).length ≤ p.length + 1

set_option maxRecDepth 100000 in
/-- Over the all-marker payloads of length `0..7`, the first whose framed encoding is longer than
the payload plus the flag is `[marker]`: the single reserved byte becomes a two-byte escape.
`[PROVED: kernel]` -/
theorem search_encode_no_expansion :
    ((List.range 8).map (fun k => List.replicate k Stuff.marker)).find?
        (fun p => !decide ((Stuff.encode p).length ≤ p.length + 1))
      = some [Stuff.marker] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `[PROVED: kernel]` -/
theorem encode_no_expansion_false : ¬ encode_no_expansion :=
  fun h => absurd (h [Stuff.marker]) (by decide +kernel)

refuted% encode_no_expansion encode_no_expansion_false search_encode_no_expansion

/-! ## 6. `CodecLaws.length_le` at `Stuff` without the domain's payload-length bound -/

/-- The rejected candidate: every payload frames inside the instance's constant `maxLen`. This is
the statement `CodecLaws.length_le` would make if `Stuff.instCodecModel.Dom` carried only the
byte-range condition and not `p.length ≤ 255`, and it is why that second conjunct is there. A
codec whose encoding grows with its input cannot be bounded by a constant on an unbounded
domain. -/
def stuff_maxLen_unbounded : Prop := ∀ p : List Nat, (Stuff.encode p).length ≤ 2 * 255 + 1

set_option maxRecDepth 1000000 in
/-- Over the all-marker payloads of lengths `0, 64, 128, 192, 256`, the first to overrun the
constant bound is the 256-byte one: stuffing doubles it to 512 bytes, and the flag makes 513.
`[PROVED: kernel]` -/
theorem search_stuff_maxLen_unbounded :
    ([0, 64, 128, 192, 256].map (fun k => List.replicate k Stuff.marker)).find?
        (fun p => !decide ((Stuff.encode p).length ≤ 2 * 255 + 1))
      = some (List.replicate 256 Stuff.marker) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- `[PROVED: kernel]` -/
theorem stuff_maxLen_unbounded_false : ¬ stuff_maxLen_unbounded :=
  fun h => absurd (h (List.replicate 256 Stuff.marker)) (by decide +kernel)

refuted% stuff_maxLen_unbounded stuff_maxLen_unbounded_false search_stuff_maxLen_unbounded

/-! ## 7. `Zigzag.zigzag_lt` without its `i32`-range hypothesis

This is the `i32`-boundary refutation of the zigzag unit, and the one that pins the domain: it
refutes exactly the lemma that admits the composed model into `Varint`'s claimed `u32` domain.
Note what it is *not*: `zigzag_roundtrip` stripped of its hypothesis is not refuted at the `i32`
boundary at all -- `2 ^ 31` and `-(2 ^ 31) - 1` both still round-trip, because zigzag halves the
varint's five-byte reach, so the first failure is at the varint's own fuel boundary (block 9 below).
The range hypothesis is therefore evidenced here, at `zigzag_lt`, or nowhere. -/

/-- The rejected candidate: the zigzag image of every integer lies in the varint's `u32` domain. -/
def zigzag_lt_unbounded : Prop := ∀ n : Int, Zigzag.zigzag n < 2 ^ 32

/-- Over the powers of two below `2 ^ 34`, the first whose zigzag image leaves the `u32` domain is
exactly `2 ^ 31` -- the first value outside `i32`. `[PROVED: kernel]` -/
theorem search_zigzag_lt_unbounded :
    (((List.range 34).map (fun k => (2:Int) ^ k)).find?
        (fun n => !decide (Zigzag.zigzag n < 2 ^ 32))) = some ((2:Int) ^ 31) := by
  decide +kernel

/-- `[PROVED: kernel]` -/
theorem zigzag_lt_unbounded_false : ¬ zigzag_lt_unbounded :=
  fun h => absurd (h ((2:Int) ^ 31)) (by decide +kernel)

refuted% zigzag_lt_unbounded zigzag_lt_unbounded_false search_zigzag_lt_unbounded

/-! ## 8. `Zigzag.zigzag` is not order-preserving

Not a hypothesis-stripping refutation but a design record: the zigzag encoding interleaves the two
signs, so the encoded order is *not* the signed order. This is why the unit must not be used for
ordered comparison on the wire -- two encodings cannot be compared lexicographically to compare the
values they carry. -/

/-- The rejected candidate: zigzag is monotone, so encoded values compare as the signed ones do. -/
def zigzag_monotone : Prop := ∀ m n : Int, m ≤ n → Zigzag.zigzag m ≤ Zigzag.zigzag n

/-- Over the twenty-five pairs from `[-2, -1, 0, 1, 2]²`, the first ordered pair whose zigzag images
are out of order is `(-2, -1)`: `zigzag (-2) = 3` but `zigzag (-1) = 1`. `[PROVED: kernel]` -/
theorem search_zigzag_monotone :
    (([-2, -1, 0, 1, 2].flatMap fun i : Int => [-2, -1, 0, 1, 2].map fun j : Int => (i, j)).find?
      fun p => decide (p.1 ≤ p.2 ∧ ¬ Zigzag.zigzag p.1 ≤ Zigzag.zigzag p.2)) = some (-2, -1) := by
  decide +kernel

/-- `[PROVED: kernel]` -/
theorem zigzag_monotone_false : ¬ zigzag_monotone :=
  fun h => absurd (h (-2) (-1) (by decide)) (by decide +kernel)

refuted% zigzag_monotone zigzag_monotone_false search_zigzag_monotone

/-! ## 9. `Zigzag.encode_length_le` without its `i32`-range hypothesis

**Read the witness carefully.** The first failure is `2 ^ 34`, which is the *varint's* own five-byte
fuel boundary (`128 ^ 5 = 2 ^ 35`, halved by zigzag's doubling), not the `i32` boundary `2 ^ 31`.
So this block records that the length bound needs *some* domain restriction, inherited from the
codec underneath; it does **not** test the `i32` range that `Dom` names. The refutation that pins
the `i32` boundary is `zigzag_lt_unbounded` in block 7, at exactly `2 ^ 31`. -/

/-- The rejected candidate: every integer's zigzag encoding fits in five bytes. -/
def zigzag_encode_length_le_unbounded : Prop := ∀ n : Int, (Zigzag.encode n).length ≤ 5

/-- Over the powers of two below `2 ^ 40`, the first whose encoding is longer than five bytes is
`2 ^ 34` -- the varint's fuel boundary, not the `i32` boundary. `[PROVED: kernel]` -/
theorem search_zigzag_encode_length_le_unbounded :
    (((List.range 40).map (fun k => (2:Int) ^ k)).find?
        (fun n => !decide ((Zigzag.encode n).length ≤ 5))) = some ((2:Int) ^ 34) := by
  decide +kernel

/-- `[PROVED: kernel]` -/
theorem zigzag_encode_length_le_unbounded_false : ¬ zigzag_encode_length_le_unbounded :=
  fun h => absurd (h ((2:Int) ^ 34)) (by decide +kernel)

refuted% zigzag_encode_length_le_unbounded zigzag_encode_length_le_unbounded_false
  search_zigzag_encode_length_le_unbounded


/-! ## 10. RFC 1982 serial `lt` is not transitive

**This is the one countermodel in this repository that refutes a law a reader would simply assume
holds.** Every other block here refutes a statement missing a hypothesis; this one refutes
transitivity of an order-looking relation. RFC 1982 §3.2 defines the comparison and never states
that it composes, and it does not: `lt` has genuine three-cycles. That is why
`Spec/Serial.lean`'s `SerialLaws` has no transitivity field, why `Model/SeqNum/Theorems.lean` proves
no transitivity theorem, and why a `ReceiverLaws`-style consumer must not build a total order on
this relation.

**Why a step of 5000 and not powers of two.** A powers-of-two enumeration's first failure is
`(0, 16384, 32768)`, where `a` and `c` are exactly half the space apart and *neither* is serially
before the other -- that is §3.2's **undefined region**, a different phenomenon, refuted separately
in block 11 below. A step of 5000 puts the first failure at a triple that genuinely cycles:
`cycle_witness` below records that `lt 40000 0` holds too, so `0 -> 20000 -> 40000 -> 0` is a cycle
rather than a mere failure to compose. The enumeration *is* the finding, which is why it is stated
rather than tuned silently. -/

/-- The rejected candidate: serial comparison composes, i.e. `lt` is transitive. -/
def lt_trans_cand : Prop :=
  ∀ a b c : BitVec 16, SeqNum.lt a b = true → SeqNum.lt b c = true → SeqNum.lt a c = true

/-- Over the six triples `(0, d, 2 * d)` for `d` stepping by 5000, the first that breaks
transitivity is `(0, 20000, 40000)`. `[PROVED: kernel]` -/
theorem search_lt_trans :
    (([5000, 10000, 15000, 20000, 25000, 30000] : List Nat).map
        (fun d => (BitVec.ofNat 16 0, BitVec.ofNat 16 d, BitVec.ofNat 16 (2 * d)))).find?
      (fun t => SeqNum.lt t.1 t.2.1 && SeqNum.lt t.2.1 t.2.2 && !SeqNum.lt t.1 t.2.2)
      = some (0#16, 20000#16, 40000#16) := by decide +kernel

/-- `[PROVED: kernel]` -/
theorem lt_trans_cand_false : ¬ lt_trans_cand :=
  fun h => absurd (h 0#16 20000#16 40000#16 (by decide) (by decide)) (by decide)

/-- The third edge, which makes the witness a *cycle* and not merely a composition failure:
`40000` is serially before `0`. `[PROVED: kernel]` -/
theorem cycle_witness : SeqNum.lt 40000#16 0#16 = true := by decide

refuted% lt_trans_cand lt_trans_cand_false search_lt_trans

/-! ## 11. Totality of serial `lt` without the `defined` hypothesis

RFC 1982 §3.2 leaves the comparison undefined on a pair exactly half the space apart, and that
region is reachable in this formulation: `dist 0 32768 = 32768 = dist 32768 0`, so neither number is
serially before the other. This block is what makes `SerialLaws.lt_total_of_defined`'s `defined`
hypothesis demonstrably load-bearing rather than decorative -- the same service
`stuff_maxLen_unbounded` (block 6) performs for `Stuff`'s `maxPayload`. -/

/-- The rejected candidate: any two distinct sequence numbers are ordered one way or the other. -/
def lt_total_cand : Prop := ∀ a b : BitVec 16, a ≠ b → SeqNum.lt a b = true ∨ SeqNum.lt b a = true

/-- Over the eight multiples of 8192, the first that is comparable with neither direction against
`0` is `32768` -- exactly half the space. `[PROVED: kernel]` -/
theorem search_lt_total :
    ((List.range 8).map (fun k => BitVec.ofNat 16 (k * 8192))).find?
      (fun b => b != 0#16 && !(SeqNum.lt 0#16 b || SeqNum.lt b 0#16)) = some 32768#16 := by
  decide +kernel

/-- `[PROVED: kernel]` -/
theorem lt_total_cand_false : ¬ lt_total_cand :=
  fun h => by rcases h 0#16 32768#16 (by decide) with h1 | h1 <;> exact absurd h1 (by decide)

refuted% lt_total_cand lt_total_cand_false search_lt_total

#print axioms search_encode_length_le_unbounded
#print axioms encode_length_le_unbounded_false
#print axioms search_varint_roundtrip_unbounded
#print axioms varint_roundtrip_unbounded_false
#print axioms search_parseFrameResync_roundtrip
#print axioms parseFrameResync_roundtrip_false
#print axioms search_idx_ne_le
#print axioms idx_ne_le_false
#print axioms search_encode_no_expansion
#print axioms encode_no_expansion_false
#print axioms search_stuff_maxLen_unbounded
#print axioms stuff_maxLen_unbounded_false
#print axioms search_zigzag_lt_unbounded
#print axioms zigzag_lt_unbounded_false
#print axioms search_zigzag_monotone
#print axioms zigzag_monotone_false
#print axioms search_zigzag_encode_length_le_unbounded
#print axioms zigzag_encode_length_le_unbounded_false
#print axioms search_lt_trans
#print axioms lt_trans_cand_false
#print axioms cycle_witness
#print axioms search_lt_total
#print axioms lt_total_cand_false

end FramedChannel
