-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Ladder
import Std.Tactic.BVDecide
import FramedChannel.Model.SeqNum.Defs

/-!
# Model/SeqNum/Theorems: the serial-number component

`[HAND-WRITTEN: model; bridged]` -- a hand-written model of `rust/src/seq_num.rs`: RFC 1982
serial-number arithmetic over a 16-bit space. Sequence numbers are `BitVec 16`; no Mathlib is
needed, `BitVec` is core.

## The registered theorems and their routes

The unit deliberately spreads itself across the ladder rather than landing everything at `manual`.

* **`decide`.** `lt_irrefl` and `lt_succ` quantify one 16-bit variable, so the kernel decides all
  65536 cases. Both run in the `Decide16` section below, at the proof-ladder audit's own heartbeat
  budget.
* **`bv_decide`.** `lt_eq_ltRFC` -- that the one-test distance form the Rust uses agrees with RFC
  1982 §3.2's two-case formula -- quantifies *two* 16-bit variables, so `decide` is infeasible over
  2 ^ 32 pairs, and `simp_all`/`grind` were both measured failing. SAT is the natural method here,
  and this is the example's second `[PROVED: compiler-trusting]` row: its `#print axioms` shows a
  native `bv_decide` helper axiom, so it is registered `verified := false` and declared `flagged` in
  `certificate/policy.txt`.
* **`manual (excluding bv_decide)`.** `lt_eq_ltRFC_kernel` replays that same statement in the
  kernel, through `BitVec.toNat` and `omega`, with no SAT call and no compiler-trusting axiom. It
  sits *beside* the `bv_decide` row, not in place of it, exactly as `Crc8.crc8_step_linear_kernel`
  does: the row exists to avoid the `bv_decide` rung, so that rung is excluded from its audit and
  the record says so. `lt_total_of_defined` carries the same qualifier for the same structural
  reason -- any two-variable `BitVec 16` fact is inside `bv_decide`'s reach.
* **`grind`.** `dist_add`, `lt_add` and `lt_translation_invariant` each fall to one `grind` call
  given the unit's own definitions as hints. Each was first written as a `retrieval` simp call over
  named `BitVec` lemmas, and the proof-ladder audit rejected the label naming `grind`; the label
  follows the audit, not the other way round.
* **`retrieval`.** `iter_space` is one simp call over named lemmas (`iter_eq`, `ofNat_space`,
  `BitVec.add_zero`).

## What is refuted rather than proved

There is no transitivity theorem here, and there never will be: `lt` is **not** transitive.
`FramedChannel/Evidence/Countermodels.lean` refutes it in the kernel at `(0, 20000, 40000)`, a
genuine three-cycle, and refutes unguarded totality at `32768`. That is why `Spec/Serial.lean`'s
`SerialLaws` has four fields and no fifth.

## Rust to Lean mapping

| Rust `seq_num.rs`     | Lean                  |
|-----------------------|-----------------------|
| `HALF: u16 = 0x8000`  | `half`                |
| `SeqNum::succ`        | `succ`                |
| `SeqNum::add`         | `add`                  |
| `SeqNum::dist`        | `dist`                |
| `SeqNum::lt`          | `lt` (and `ltRFC`, proved equal) |
-/

namespace FramedChannel.SeqNum

/-! ## The space closes after exactly `space` steps -/

/-- Iterating `succ` is adding the step count. `[PROVED: kernel]` -/
theorem iter_eq (k : Nat) (n : BitVec 16) : iter k n = n + BitVec.ofNat 16 k := by
  induction k with
  | zero => simp [iter]
  | succ k ih => simp [iter, ih, succ, BitVec.ofNat_add, BitVec.add_assoc]

/-- The space size is `0` in the space. `[PROVED: kernel]` -/
theorem ofNat_space : BitVec.ofNat 16 space = 0#16 := by decide

/-- `space` successor steps return to where they started. `[PROVED: kernel]` -/
theorem iter_space (n : BitVec 16) : iter space n = n := by
  rung retrieval => simp only [iter_eq, ofNat_space, BitVec.add_zero]

/-- And no fewer: the cycle is *exactly* `space` long. This is the minimality half of "exactly
`space` steps"; it is registered here rather than made a `SerialLaws` field, because it constrains
the model rather than the consumer (`certificate/seq_num.yaml`'s `guarantees:` records the split).
`[PROVED: kernel]` -/
theorem iter_ne_of_pos_lt (k : Nat) (hk : 0 < k) (hks : k < space) (n : BitVec 16) :
    iter k n ≠ n := by
  rung manual =>
    rw [iter_eq]
    intro h
    have h2 := congrArg BitVec.toNat h
    have hn := n.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2
    unfold space at hks
    omega

/-! ## The distance, the increment and the successor -/

/-- The forward distance recovers the increment: `dist` is the left inverse of `add`.
`[PROVED: kernel]` -/
theorem dist_add (n k : BitVec 16) : dist n (add n k) = k := by
  rung grind => grind [dist, add]

/-- RFC 1982 §3.1's claim: advancing by a positive increment below half the space lands strictly
after where you started. Both hypotheses are needed -- `0#16 < k` because `add n 0 = n` is not
serially after `n`, and `k < half` because beyond half the space the comparison points the other
way. `[PROVED: kernel]` -/
theorem lt_add (n k : BitVec 16) (h0 : 0#16 < k) (hh : k < half) : lt n (add n k) = true := by
  rung grind => grind [lt, dist, add, half]

/-- Advancing both arguments leaves the comparison unchanged.

This answers the RFC passage a reader is most likely to misread. §3.2 remarks that for *some*
definition of the comparison one could have `s1 < s2` while `(s1 + 1) > (s2 + 1)`; that remark is
about a definition the RFC **rejected**. This formulation does not have the defect, and the fact is
a kernel-checked row rather than a comment. `[PROVED: kernel]` -/
theorem lt_translation_invariant (a b : BitVec 16) : lt (succ a) (succ b) = lt a b := by
  rung grind => grind [lt, dist, half, succ]

/-! ## Totality, on the defined region only

RFC 1982 §3.2 leaves the comparison undefined on a pair exactly half the space apart, and that
region is reachable: `dist 0 32768 = 32768 = dist 32768 0`, so neither number is serially before
the other. The `defined` hypothesis below is therefore not removable, and
`Evidence/Countermodels.lean` refutes the statement without it. -/

/-- Two distinct numbers that are not half the space apart are ordered one way or the other.
`[PROVED: kernel]` -/
theorem lt_total_of_defined (a b : BitVec 16) (hne : a ≠ b) (hd : defined a b = true) :
    lt a b = true ∨ lt b a = true := by
  rung manual (excluding bv_decide) =>
    simp only [defined, bne_iff_ne, ne_eq] at hd
    have ha := a.isLt
    have hb := b.isLt
    have hp : (2 : Nat) ^ 16 = 65536 := by decide
    have hne' : a.toNat ≠ b.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
    have hh' : ((2 ^ 16 - a.toNat) + b.toNat) % 2 ^ 16 ≠ 32768 := by
      intro h
      exact hd (by unfold dist half; apply BitVec.eq_of_toNat_eq; simpa using h)
    simp only [lt, dist, half, Bool.and_eq_true, decide_eq_true_eq, BitVec.lt_def,
      BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

/-! ## RFC 1982 §3.2: the two spellings agree

`lt` is the one modular-distance test an implementation writes; `ltRFC` is the RFC's two-case
formula transcribed literally. Their agreement is what makes "faithful to RFC 1982" an auditable
claim rather than a comment, and it is where this unit's `bv_decide` rung comes from: over `2 ^ 32`
pairs `decide` is infeasible, and `simp_all`/`grind` were both measured failing. -/

/-- The RFC's formula and the distance test agree on every pair.

`[PROVED: compiler-trusting]` (`bv_decide`): its `#print axioms` carries a native helper axiom, so
the row is registered unverified and declared `flagged` in `certificate/policy.txt`. Its kernel
replay is `lt_eq_ltRFC_kernel` below, registered beside it. -/
theorem lt_eq_ltRFC (a b : BitVec 16) : ltRFC a b = lt a b := by
  rung bv_decide =>
    simp only [ltRFC, lt, dist, half]
    bv_decide

/-- Kernel replay of `lt_eq_ltRFC`, with no `bv_decide` and no compiler-trusting axiom: both
spellings are read through `BitVec.toNat` and the equivalence is arithmetic. `[PROVED: kernel]` -/
theorem lt_eq_ltRFC_kernel (a b : BitVec 16) : ltRFC a b = lt a b := by
  -- The row exists to avoid `bv_decide`, so that rung is excluded from its audit, and the record
  -- says so.
  rung manual (excluding bv_decide) =>
    have ha := a.isLt
    have hb := b.isLt
    have hp : (2 : Nat) ^ 16 = 65536 := by decide
    rw [Bool.eq_iff_iff]
    simp only [ltRFC, lt, dist, half, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

/-! ## The two single-variable facts, decided in the kernel

One 16-bit variable is 65536 cases, which plain `decide` settles -- the cheapest rung on the
ladder, and a higher label fails the build naming it. The section raises the heartbeat budget to the
proof-ladder audit's own (`Ladder.auditHeartbeats`), since the default 200000 is not enough for a
65536-case kernel reduction. -/

section Decide16
set_option maxHeartbeats 20000000

/-- No number is serially before itself. `[PROVED: kernel]` -/
theorem lt_irrefl (n : BitVec 16) : lt n n = false := by
  rung decide => decide +revert

/-- Every number is serially before its successor. `[PROVED: kernel]` -/
theorem lt_succ (n : BitVec 16) : lt n (succ n) = true := by
  rung decide => decide +revert

end Decide16

/-! ## The interface instance

`SerialModel` (L0) and `SerialLaws` (L1) are specification, declared in `Spec/Serial.lean`. The
instance is the refinement certificate in interface terms: the canonical model satisfies exactly the
four laws serial arithmetic supports, and no transitivity law, because there is none to satisfy. -/

/-- The interface's derived iterate at `Serial` is the model's structural `iter` on the wrapped
value. `[PROVED: kernel]` -/
theorem iter_serial (k : Nat) (s : Serial) :
    SerialModel.iter k s = ⟨iter k s.value⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show SerialModel.succ (SerialModel.iter k s) = _
    rw [ih]
    rfl

/-- The refinement certificate as an interface instance: the canonical 16-bit model satisfies the
serial-number laws. `[PROVED: kernel]` -/
instance instSerialLaws : SerialLaws Serial where
  lt_irrefl n := lt_irrefl n.value
  lt_succ n := lt_succ n.value
  succ_cycles n := by
    show SerialModel.iter space n = n
    rw [iter_serial, iter_space]
  lt_total_of_defined a b hne hd :=
    lt_total_of_defined a.value b.value (fun h => hne (by cases a; cases b; simp_all)) hd

ladder_record% instSerialLaws instance

#print axioms iter_eq
#print axioms ofNat_space
#print axioms iter_space
#print axioms iter_ne_of_pos_lt
#print axioms dist_add
#print axioms lt_add
#print axioms lt_translation_invariant
#print axioms lt_total_of_defined
#print axioms lt_eq_ltRFC
#print axioms lt_eq_ltRFC_kernel
#print axioms lt_irrefl
#print axioms lt_succ
#print axioms iter_serial
#print axioms instSerialLaws

end FramedChannel.SeqNum
