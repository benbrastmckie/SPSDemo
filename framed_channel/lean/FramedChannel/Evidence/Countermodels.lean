-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import FramedChannel.Model.Varint.Theorems
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

#print axioms search_encode_length_le_unbounded
#print axioms encode_length_le_unbounded_false
#print axioms search_varint_roundtrip_unbounded
#print axioms varint_roundtrip_unbounded_false
#print axioms search_parseFrameResync_roundtrip
#print axioms parseFrameResync_roundtrip_false
#print axioms search_idx_ne_le
#print axioms idx_ne_le_false

end FramedChannel
