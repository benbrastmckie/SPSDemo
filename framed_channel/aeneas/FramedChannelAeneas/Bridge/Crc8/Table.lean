-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.Crc8.Defs
import FramedChannel.Model.Crc8.Theorems

/-!
# Bridge/Crc8/Table: the extracted table-driven `crc8_table` refines the model's `crc8Table`

`[EXTRACTED: aeneas + bridge]` -- the table implementation of `rust/src/crc8.rs`, as
extracted (`Extracted/Funs.lean`: the constant `crc8.TABLE` and a `loop` over the slice iterator
that looks each byte up with `TABLE.get(..)`), against `FramedChannel.Crc8.crc8Table`
(`lean/FramedChannel/Model/Crc8/Theorems.lean`).

* `table_agrees`: the extracted 256-entry `TABLE` is the model's `table`, entry for entry, by
  kernel `decide` (under a raised recursion depth, as the model's own `table_entry` needs).
* `table_index`: the lookup index `(crc ^ b) as usize` keeps its value through the cast and is
  inside the table -- the extracted counterpart of the model's `stepTable_index_in_range`. So the
  Rust `unwrap_or(0)` fallback (the extraction's `none => 0` branch) is dead code, proved here.
* `table_entry_bv`: an entry the lookup returns is the model's `stepTable`.
* `table_loop_refines`, `crc8_table_refines`: the loop is the model's fold, from seed `0`.

The triple is total correctness: the extracted `crc8_table` never panics on any slice.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.crc8
open framed_channel

section KernelDecide
set_option maxRecDepth 100000

/-- Table agreement: the extracted `TABLE` is the model's table, entry for entry.
`[EXTRACTED: aeneas + bridge]` -/
theorem table_agrees : crc8.TABLE.val.map (·.bv) = FramedChannel.Crc8.table.toList := by
  unfold crc8.TABLE
  decide +kernel

end KernelDecide

/-- The extracted table has 256 entries. -/
theorem table_length : crc8.TABLE.val.length = 256 := by
  simp

/-- The table index: the `u8`-to-`usize` cast of `crc ^ b` keeps its value, which is inside the
table, so `TABLE.get(..)`'s `None` branch is dead. -/
theorem table_index (c b : Std.U8) :
    (UScalar.cast .Usize (c ^^^ b)).val = (c.bv ^^^ b.bv).toNat ∧
      (c.bv ^^^ b.bv).toNat < crc8.TABLE.val.length := by
  rw [table_length]
  have h1 : (c ^^^ b).val < 256 := (c ^^^ b).hBounds
  refine ⟨?_, (c.bv ^^^ b.bv).isLt⟩
  have : (UScalar.cast .Usize (c ^^^ b)).val = (c ^^^ b).val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have : 2 ^ 8 ≤ 2 ^ UScalarTy.Usize.numBits := by
      apply Nat.pow_le_pow_right (by omega)
      cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]
    omega
  rw [this]
  rfl

/-- A table entry the extracted lookup returns is the model's table step. -/
theorem table_entry_bv (c b v : Std.U8)
    (h : crc8.TABLE.val[(c.bv ^^^ b.bv).toNat]? = some v) :
    v.bv = FramedChannel.Crc8.stepTable c.bv b.bv := by
  have h2 : (crc8.TABLE.val.map (·.bv))[(c.bv ^^^ b.bv).toNat]? = some v.bv := by
    rw [List.getElem?_map, h]
    rfl
  rw [table_agrees, Array.getElem?_toList] at h2
  obtain ⟨hlt, hv⟩ := Array.getElem?_eq_some_iff.mp h2
  unfold FramedChannel.Crc8.stepTable
  simp only [Array.getD, dif_pos hlt]
  exact hv.symm

/-- The table loop invariant, over `(slice iterator, crc)`. -/
def TableInv (s : Slice Std.U8) (x : core.slice.iter.Iter Std.U8 × Std.U8) : Prop :=
  x.1.slice = s ∧ x.1.i ≤ s.val.length ∧
    x.2.bv = ((bitsOf s.val).take x.1.i).foldl FramedChannel.Crc8.stepTable 0

/-- The table loop lemma: from any state satisfying `TableInv`, the loop ends at the model's table
digest of the whole slice. -/
theorem table_loop_refines (s : Slice Std.U8) (x : core.slice.iter.Iter Std.U8 × Std.U8)
    (hx : TableInv s x) :
    crc8.crc8_table_loop x.1 x.2 ⦃ c => c.bv = FramedChannel.Crc8.crc8Table (bitsOf s.val) ⦄ := by
  unfold crc8.crc8_table_loop
  apply loop.spec_decr_nat
    (measure := fun (x : core.slice.iter.Iter Std.U8 × Std.U8) => s.val.length - x.1.i)
    (inv := TableInv s)
  · rintro ⟨it, crc⟩ ⟨hsl, hi, heq⟩
    simp only at hsl hi heq
    subst hsl
    unfold crc8.crc8_table_loop.body
    step*
    · have hon : o = none := by assumption
      rw [hon] at o_post
      have hge : it.slice.val.length ≤ it.i := List.getElem?_eq_none_iff.mp o_post.symm
      rw [heq, FramedChannel.Crc8.crc8Table, List.take_of_length_le (by simp [bitsOf]; omega)]
    all_goals
      have hob : o = some b := by assumption
      rw [hob] at o_post
      obtain ⟨hlt, hb⟩ := List.getElem?_eq_some_iff.mp o_post.symm
      simp only [hlt, if_true] at o_post2
      obtain ⟨hidx, hin⟩ := table_index crc b
      have hs : s.val = crc8.TABLE.val := by rw [s_post]; simp [Array.to_slice]
      have hieq : i = crc ^^^ b := UScalar.eq_of_val_eq i_post
      rw [i1_post, hieq, hs] at o1_post
    · exfalso
      have hon : o1 = none := by assumption
      rw [hon, hidx] at o1_post
      exact absurd (List.getElem?_eq_none_iff.mp o1_post.symm) (by omega)
    · have hov : o1 = some v := by assumption
      rw [hov, hidx] at o1_post
      have hv := table_entry_bv crc b v o1_post.symm
      refine ⟨⟨o_post1, by simp only; omega, ?_⟩, by rw [o_post2]; omega⟩
      simp only
      have htake : (bitsOf it.slice.val).take (it.i + 1) =
          (bitsOf it.slice.val).take it.i ++ [b.bv] := by
        rw [List.take_add_one]
        simp [bitsOf, List.getElem?_map, List.getElem?_eq_getElem hlt, hb]
      rw [o_post2, htake, List.foldl_append, ← heq, List.foldl_cons, List.foldl_nil]
      exact hv
  · exact hx

/-- Table refinement: the extracted `crc8_table` never fails, and computes the model's table CRC
of the slice's bytes. `[EXTRACTED: aeneas + bridge]` -/
theorem crc8_table_refines (s : Slice Std.U8) :
    crc8.crc8_table s ⦃ c => c.bv = FramedChannel.Crc8.crc8Table (bitsOf s.val) ⦄ := by
  unfold crc8.crc8_table
  step*
  exact table_loop_refines s (iter, 0#u8)
    ⟨s_post, by simp only [iter_post]; omega, by simp only [iter_post]; rfl⟩

end FramedChannel.Bridge.crc8

#print axioms FramedChannel.Bridge.crc8.table_agrees
#print axioms FramedChannel.Bridge.crc8.table_length
#print axioms FramedChannel.Bridge.crc8.table_index
#print axioms FramedChannel.Bridge.crc8.table_entry_bv
#print axioms FramedChannel.Bridge.crc8.table_loop_refines
#print axioms FramedChannel.Bridge.crc8.crc8_table_refines
