-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.SeqNum.Defs
import FramedChannel.Model.SeqNum.Theorems

/-!
# Bridge/SeqNum/Instance: the extracted serial arithmetic refines the model's, and `SerialLaws`

`[EXTRACTED: aeneas + bridge]` -- the serial-number rows, stated about the Rust as extracted.

## One total-correctness triple per extracted operation

`new`, `get`, `succ`, `add`, `dist` and `lt` each get their own triple, so the theorems rule out
every failure of the extracted code as well as fixing its result. **None carries a hypothesis**, and
that is the finding rather than an accident: `core.num.U16.wrapping_add` and `wrapping_sub` are
*pure* `U16 -> U16 -> U16` functions in Aeneas's library, not `Result`-valued ones, so wraparound is
not a failure to exclude -- it is the definition. Contrast `varint.encode_refines`, which must carry
`out.length + 5 <= Usize.max` for its `Vec::push` overflow obligation.

Every arithmetic obligation closes through `core.num.U16.wrapping_add_bv_eq` /
`wrapping_sub_bv_eq`, which state the machine operations *directly* as `BitVec 16` arithmetic on
`.bv`. That is the whole return on `Model/SeqNum/Defs.lean`'s recorded decision to represent a
sequence number as `BitVec 16` rather than as `Nat` with an explicit modulus: the abstraction is a
field read, so there is nothing to reconcile.

`lt_refines` is the one proof with real content, because the extracted `lt` branches on the
zero test first (`if d != 0 then d < HALF else false`) where the model conjoins
(`0 < dist && dist < half`). Both branches reduce to `Nat` arithmetic on `d.val` and close by
`omega`. **No `bv_decide` appears anywhere in this file**: a native helper axiom here would mean a
second `flagged` row in `certificate/policy.txt` for a fact `omega` settles.

`HALF_val` and `half_eq` read the extracted `pub const` once, in the shape
`Bridge/Stuff/Stuff.lean`'s `MARKER_val` / `ESC_val` set. This is not decoration: the extraction
emits a `const` as its own `irreducible` definition, so `framed_channel.seq_num.HALF` is a selection
candidate in its own right and the gate's selection-reach stage demands a registered statement about
it exactly as it does for each function.

## The interface instance

`instSerialLaws_extracted` is `SerialLaws` at the extracted carrier `seq_num.SeqNum` itself -- no
component tag, because `SerialModel` is indexed by the representation. Per step 9.5's two-part test
no `SerialSim` is owed (`SeqNum` dispatches through no trait, and no composite is proved generic
over it), so none is built. `succ_cycles` goes through `ext_iter`, which pushes the abstraction
through the interface's derived `SerialModel.iter`, and then through `toModel_inj` -- available
because the abstraction is a bijection rather than a projection.

**There is no transitivity law here either**, for the same reason there is none at the model: RFC
1982's serial comparison has genuine three-cycles, refuted in the kernel in
`lean/FramedChannel/Evidence/Countermodels.lean` at `(0, 20000, 40000)`.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.seq_num
open framed_channel

/-! ## The extracted constant, read once -/

/-- The extracted `HALF` is `2 ^ 15`. `[EXTRACTED: aeneas + bridge]` -/
theorem HALF_val : seq_num.HALF.val = 32768 := by simp [seq_num.HALF]

/-- The model's `half` is the extracted `HALF`'s bit vector. `[EXTRACTED: aeneas + bridge]` -/
theorem half_eq : seq_num.HALF.bv = FramedChannel.SeqNum.half := by
  simp [seq_num.HALF, FramedChannel.SeqNum.half]

/-! ## The abstraction is a bijection, not a projection -/

/-- `ofModel` is a right inverse of `toModel`. -/
theorem toModel_ofModel (b : BitVec 16) : toModel (ofModel b) = b := rfl

/-- `ofModel` is a left inverse of `toModel`: nothing is lost. -/
theorem ofModel_toModel (s : seq_num.SeqNum) : ofModel (toModel s) = s := rfl

/-- `toModel` is injective, which is what lets a model equation be pushed back to the extracted
carrier (`succ_cycles` below needs exactly this). -/
theorem toModel_inj {a b : seq_num.SeqNum} (h : toModel a = toModel b) : a = b := by
  rw [← ofModel_toModel a, ← ofModel_toModel b, h]

/-- The contrapositive, in the shape `SerialLaws.lt_total_of_defined` consumes. -/
theorem toModel_ne (a b : seq_num.SeqNum) (h : a ≠ b) : toModel a ≠ toModel b :=
  fun he => h (toModel_inj he)

/-! ## Refinement, one triple per extracted operation -/

/-- The extracted constructor stores exactly the word it is given. `[EXTRACTED: aeneas + bridge]` -/
theorem new_refines (v : Std.U16) :
    seq_num.SeqNum.new v ⦃ s => toModel s = v.bv ⦄ := by
  unfold seq_num.SeqNum.new
  step*
  simp [toModel]

/-- The extracted accessor returns exactly the stored word, so `new` and `get` are inverse.
`[EXTRACTED: aeneas + bridge]` -/
theorem get_refines (s : seq_num.SeqNum) :
    seq_num.SeqNum.get s ⦃ v => v.bv = toModel s ⦄ := by
  unfold seq_num.SeqNum.get
  step*
  simp [toModel]

/-- The extracted successor is the model's `succ` under the abstraction, with no failure case and no
hypothesis: `wrapping_add` cannot overflow. `[EXTRACTED: aeneas + bridge]` -/
theorem succ_refines (s : seq_num.SeqNum) :
    seq_num.SeqNum.succ s ⦃ r => toModel r = FramedChannel.SeqNum.succ (toModel s) ⦄ := by
  unfold seq_num.SeqNum.succ
  step*
  simp_all [toModel, FramedChannel.SeqNum.succ]

/-- The extracted bounded increment is the model's `add` under the abstraction. RFC 1982 §3.1's
`0 < n < 2 ^ 15` is a condition on the *claim* `lt n (add n k)`, not on this operation, which is
total. `[EXTRACTED: aeneas + bridge]` -/
theorem add_refines (s : seq_num.SeqNum) (n : Std.U16) :
    seq_num.SeqNum.add s n ⦃ r => toModel r = FramedChannel.SeqNum.add (toModel s) n.bv ⦄ := by
  unfold seq_num.SeqNum.add
  step*
  simp_all [toModel, FramedChannel.SeqNum.add]

/-- The extracted forward distance is the model's `dist` under the abstraction.
`[EXTRACTED: aeneas + bridge]` -/
theorem dist_refines (a b : seq_num.SeqNum) :
    seq_num.SeqNum.dist a b ⦃ d => d.bv = FramedChannel.SeqNum.dist (toModel a) (toModel b) ⦄ := by
  unfold seq_num.SeqNum.dist
  step*
  simp_all [toModel, FramedChannel.SeqNum.dist]

/-- The extracted serial comparison is the model's `lt` under the abstraction: the machine's
zero-test-then-compare shape agrees with the model's conjunction on every pair, both branches by
`omega` rather than by SAT. `[EXTRACTED: aeneas + bridge]` -/
theorem lt_refines (a b : seq_num.SeqNum) :
    seq_num.SeqNum.lt a b ⦃ r => r = FramedChannel.SeqNum.lt (toModel a) (toModel b) ⦄ := by
  unfold seq_num.SeqNum.lt
  step*
  · rename_i h
    have hd : FramedChannel.SeqNum.dist (toModel a) (toModel b) = d.bv := by
      simp [d_post, toModel, FramedChannel.SeqNum.dist]
    have h0 : 0 < d.val := by
      have hne : ¬ (d.val = 0) := by simpa using h
      omega
    rw [Bool.eq_iff_iff]
    simp only [FramedChannel.SeqNum.lt, hd, FramedChannel.SeqNum.half, Bool.and_eq_true,
      decide_eq_true_eq, BitVec.lt_def, BitVec.toNat_ofNat, UScalar.lt_equiv, HALF_val,
      U16.bv_toNat]
    omega
  · rename_i h
    have hd : FramedChannel.SeqNum.dist (toModel a) (toModel b) = d.bv := by
      simp [d_post, toModel, FramedChannel.SeqNum.dist]
    have hz : d.val = 0 := by simpa using h
    symm
    simp only [FramedChannel.SeqNum.lt, hd, FramedChannel.SeqNum.half, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, BitVec.lt_def, BitVec.toNat_ofNat, U16.bv_toNat]
    left
    omega

/-! ## The lowered operations are the extracted ones

Each `ext*` of `Defs.lean` is read off its triple by `WP.spec_imp_exists`: a total-correctness spec
says the call *is* an `ok`, so the lowering's fallback branch is unreachable and the lowered value is
the model's. Nothing is reproved here. -/

/-- The lowered successor is the model's `succ`. -/
theorem extSucc_toModel (s : seq_num.SeqNum) :
    toModel (extSucc s) = FramedChannel.SeqNum.succ (toModel s) := by
  obtain ⟨y, hy, hp⟩ := WP.spec_imp_exists (succ_refines s)
  simp [extSucc, hy, Result.match.ok, hp]

/-- The lowered increment is the model's `add`. -/
theorem extAdd_toModel (s : seq_num.SeqNum) (n : Std.U16) :
    toModel (extAdd s n) = FramedChannel.SeqNum.add (toModel s) n.bv := by
  obtain ⟨y, hy, hp⟩ := WP.spec_imp_exists (add_refines s n)
  simp [extAdd, hy, Result.match.ok, hp]

/-- The lowered distance is the model's `dist`. -/
theorem extDist_bv (a b : seq_num.SeqNum) :
    (extDist a b).bv = FramedChannel.SeqNum.dist (toModel a) (toModel b) := by
  obtain ⟨y, hy, hp⟩ := WP.spec_imp_exists (dist_refines a b)
  simp [extDist, hy, Result.match.ok, hp]

/-- The lowered comparison is the model's `lt`. -/
theorem extLt_eq (a b : seq_num.SeqNum) :
    extLt a b = FramedChannel.SeqNum.lt (toModel a) (toModel b) := by
  obtain ⟨y, hy, hp⟩ := WP.spec_imp_exists (lt_refines a b)
  simp [extLt, hy, Result.match.ok, hp]

/-- The lowered defined-region test is the model's `defined`. -/
theorem extDefined_eq (a b : seq_num.SeqNum) :
    extDefined a b = FramedChannel.SeqNum.defined (toModel a) (toModel b) := by
  have h : (extDist a b = seq_num.HALF) ↔
      (FramedChannel.SeqNum.dist (toModel a) (toModel b) = FramedChannel.SeqNum.half) := by
    rw [UScalar.eq_equiv_bv_eq]
    simp only [extDist_bv, half_eq]
  simp only [extDefined, FramedChannel.SeqNum.defined]
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, not_iff_not]
  exact h

/-! ## The interface instance at the extracted carrier -/

/-- The abstraction commutes with the interface's derived iterate. -/
theorem ext_iter (k : Nat) (s : seq_num.SeqNum) :
    toModel (SerialModel.iter k s) = FramedChannel.SeqNum.iter k (toModel s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show toModel (extSucc (SerialModel.iter k s)) = _
    rw [extSucc_toModel, ih]
    rfl

/-- The refinement certificate as an interface instance: the extracted 16-bit sequence number
satisfies the serial-number laws, each discharged from the corresponding model theorem through the
refinement triples above. `[EXTRACTED: aeneas + bridge]` -/
instance instSerialLaws_extracted : SerialLaws seq_num.SeqNum where
  lt_irrefl n := by
    show extLt n n = false
    rw [extLt_eq]
    exact FramedChannel.SeqNum.lt_irrefl (toModel n)
  lt_succ n := by
    show extLt n (extSucc n) = true
    rw [extLt_eq, extSucc_toModel]
    exact FramedChannel.SeqNum.lt_succ (toModel n)
  succ_cycles n := by
    apply toModel_inj
    rw [ext_iter]
    exact FramedChannel.SeqNum.iter_space (toModel n)
  lt_total_of_defined a b hne hd := by
    show extLt a b = true ∨ extLt b a = true
    rw [extLt_eq, extLt_eq]
    exact FramedChannel.SeqNum.lt_total_of_defined (toModel a) (toModel b) (toModel_ne a b hne)
      (by rw [← extDefined_eq]; exact hd)

#print axioms FramedChannel.Bridge.seq_num.HALF_val
#print axioms FramedChannel.Bridge.seq_num.half_eq
#print axioms FramedChannel.Bridge.seq_num.toModel_ofModel
#print axioms FramedChannel.Bridge.seq_num.ofModel_toModel
#print axioms FramedChannel.Bridge.seq_num.toModel_inj
#print axioms FramedChannel.Bridge.seq_num.toModel_ne
#print axioms FramedChannel.Bridge.seq_num.new_refines
#print axioms FramedChannel.Bridge.seq_num.get_refines
#print axioms FramedChannel.Bridge.seq_num.succ_refines
#print axioms FramedChannel.Bridge.seq_num.add_refines
#print axioms FramedChannel.Bridge.seq_num.dist_refines
#print axioms FramedChannel.Bridge.seq_num.lt_refines
#print axioms FramedChannel.Bridge.seq_num.extSucc_toModel
#print axioms FramedChannel.Bridge.seq_num.extAdd_toModel
#print axioms FramedChannel.Bridge.seq_num.extDist_bv
#print axioms FramedChannel.Bridge.seq_num.extLt_eq
#print axioms FramedChannel.Bridge.seq_num.extDefined_eq
#print axioms FramedChannel.Bridge.seq_num.ext_iter
#print axioms FramedChannel.Bridge.seq_num.instSerialLaws_extracted

end FramedChannel.Bridge.seq_num
