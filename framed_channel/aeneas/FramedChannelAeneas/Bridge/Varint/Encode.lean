-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.Varint.Defs
import FramedChannel.Model.Varint.Theorems

/-!
# Bridge/Varint/Encode: the extracted `encode_u32` refines the LEB128 model's `encode`

`[EXTRACTED: aeneas + bridge]` -- `encode_refines` proves that the Charon/Aeneas
extraction of `rust/src/varint.rs`'s `encode_u32` (`Extracted/Funs.lean`, a `loop` over the `i32`
range `0..5`) appends to its output vector exactly the bytes `FramedChannel.Varint.encode`
(`lean/FramedChannel/Model/Varint/Theorems.lean`) computes, read through `bytesOf`.

The triple is total correctness, so the theorem also rules out every failure of the extracted
code: the `u32` shift `n >> 7` (in range), the `u32` mask and the `u32`-to-`u8` cast (both
total), the `u8` `| 128` (total) and each `Vec::push`, whose overflow obligation is the one
hypothesis, `out.len() + 5 <= usize::MAX` (the loop pushes at most five bytes). The loop's
`None` branch -- five groups emitted and the value still non-zero -- is shown unreachable from
`n < 2^32 <= 128^5`, and `2^32` is the machine bound of `n : Std.U32` itself, not a hypothesis.

The proof is one application of Aeneas's `loop.spec_decr_nat`, with measure `end - start` over
the range and the invariant `EncInv`: after `k` iterations, `k` bytes have been pushed, the
remaining value is below `128^(5-k)` (and non-zero once `k > 0`), and the bytes pushed so far
followed by the model's `encodeF (5-k)` on the remaining value are the full model encoding.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.varint
open framed_channel

/-! ## Scalar facts: the machine operations the loop body performs, as `Nat` arithmetic -/

theorem u32_and_127 (n : Std.U32) : (n &&& 127#u32).val = n.val % 128 := by
  rw [UScalar.val_and]
  exact Nat.and_two_pow_sub_one_eq_mod n.val 7

theorem u32_cast_u8_of_lt (i : Std.U32) (h : i.val < 256) : (UScalar.cast .U8 i).val = i.val := by
  rw [UScalar.cast_val_eq]
  simp only [UScalarTy.numBits]
  exact Nat.mod_eq_of_lt h

theorem u8_or_128 (g : Std.U8) (h : g.val < 128) : (g ||| 128#u8).val = g.val + 128 := by
  rw [UScalar.val_or]
  have := Nat.two_pow_add_eq_or_of_lt (i := 7) h 1
  simp only [Nat.mul_one] at this
  show g.val ||| 128 = g.val + 128
  rw [Nat.or_comm, ← this, Nat.add_comm]

theorem shiftRight_7 (v : Nat) : v >>> 7 = v / 128 := Nat.shiftRight_eq_div_pow v 7

/-- The loop invariant, over the loop state `(range, remaining value, output)`. -/
def EncInv (n0 : Std.U32) (out0 : alloc.vec.Vec Std.U8)
    (x : core.ops.range.Range Std.I32 × Std.U32 × alloc.vec.Vec Std.U8) : Prop :=
  ∃ k : Nat, k ≤ 5 ∧ x.1.start.val = k ∧ x.1.end.val = 5 ∧
    x.2.2.length = out0.length + k ∧ x.2.1.val < 128 ^ (5 - k) ∧ (0 < k → x.2.1.val ≠ 0) ∧
    bytesOf x.2.2.val ++ FramedChannel.Varint.encodeF (5 - k) x.2.1.val =
      bytesOf out0.val ++ FramedChannel.Varint.encode n0.val

/-- The loop lemma: from any state satisfying `EncInv`, the extracted loop ends with the full model
encoding appended. -/
theorem encode_loop_refines (n0 : Std.U32) (out0 : alloc.vec.Vec Std.U8)
    (h : out0.length + 5 ≤ Usize.max)
    (x : core.ops.range.Range Std.I32 × Std.U32 × alloc.vec.Vec Std.U8) (hx : EncInv n0 out0 x) :
    varint.encode_u32_loop x.1 x.2.1 x.2.2
      ⦃ v => bytesOf v.val = bytesOf out0.val ++ FramedChannel.Varint.encode n0.val ⦄ := by
  unfold varint.encode_u32_loop
  apply loop.spec_decr_nat
    (measure := fun (x : core.ops.range.Range Std.I32 × Std.U32 × alloc.vec.Vec Std.U8) =>
      (x.1.end.val - x.1.start.val).toNat)
    (inv := EncInv n0 out0)
  · rintro ⟨it, n, out⟩ ⟨k, hk5, hks, hke, hlen, hlt, hnz, heq⟩
    simp only at hks hke hlen hlt hnz heq
    unfold varint.encode_u32_loop.body
    step*
    · -- the range is exhausted: unreachable, the value would be zero after a non-zero group
      exfalso
      have hk : k = 5 := by
        by_contra hne
        have hc : it.start.val < it.end.val := by omega
        simp only [hc, if_true] at o_post
        simp_all
      subst hk
      simp only [Nat.sub_self, Nat.pow_zero] at hlt
      exact hnz (by omega) (by omega)
    all_goals
      have hc : it.start.val < it.end.val := by
        by_contra hc
        simp only [hc, if_false] at o_post
        simp_all
      have hk : k < 5 := by omega
      obtain ⟨f, hf⟩ : ∃ f, 5 - k = f + 1 := ⟨4 - k, by omega⟩
    · simp only [alloc.vec.Vec.length] at hlen h ⊢; omega
    · have h0 : n1 = 0#u32 := by assumption
      have hn128 : n.val < 128 := by
        have : n1.val = 0 := by rw [h0]; rfl
        rw [n1_post, shiftRight_7] at this
        omega
      have hi : i.val = n.val := by rw [i_post, u32_and_127]; omega
      have hg : group.val = n.val := by
        rw [group_post, u32_cast_u8_of_lt i (by omega), hi]
      rw [hf] at heq
      simp only [FramedChannel.Varint.encodeF, if_pos hn128] at heq
      rw [← heq, out1_post]
      simp [bytesOf, hg]
    · simp only [alloc.vec.Vec.length] at hlen h ⊢; omega
    · have hne : ¬ n1 = 0#u32 := by assumption
      have hn1ne : n1.val ≠ 0 := fun hv => hne (UScalar.eq_of_val_eq (by rw [hv]; rfl))
      have hn1v : n1.val = n.val / 128 := by rw [n1_post, shiftRight_7]
      have hn128 : ¬ n.val < 128 := by omega
      have hi : i.val = n.val % 128 := by rw [i_post, u32_and_127]
      have hg : group.val = n.val % 128 := by
        rw [group_post, u32_cast_u8_of_lt i (by omega), hi]
      have hi1 : i1.val = n.val % 128 + 128 := by
        rw [i1_post, u8_or_128 group (by omega), hg]
      simp only [hc, if_true] at o_post
      obtain ⟨-, hstart⟩ := o_post
      rw [hf] at heq
      simp only [FramedChannel.Varint.encodeF, if_neg hn128] at heq
      refine ⟨⟨k + 1, by omega, by rw [hstart, hks]; push_cast; ring_nf, by rw [o_post1]; exact hke,
        ?_, ?_, fun _ => hn1ne, ?_⟩, ?_⟩
      · simp only [alloc.vec.Vec.length] at hlen ⊢
        rw [out1_post, List.length_append, hlen]
        simp only [List.length_singleton]
        omega
      · have hf' : 5 - (k + 1) = f := by omega
        rw [hf', hn1v, Nat.div_lt_iff_lt_mul (by omega)]
        rw [hf, Nat.pow_succ] at hlt
        exact hlt
      · have hf' : 5 - (k + 1) = f := by omega
        simp only
        rw [hf', ← heq, out1_post, hn1v]
        simp [bytesOf, hi1]
      · rw [hstart, o_post1]
        omega
  · exact hx

/-- Encode refinement: the extracted `encode_u32` appends exactly the model's LEB128 encoding of
`n`, and never fails, given room for five more bytes. `[EXTRACTED: aeneas + bridge]` -/
theorem encode_refines (n : Std.U32) (out : alloc.vec.Vec Std.U8)
    (h : out.length + 5 ≤ Usize.max) :
    varint.encode_u32 n out
      ⦃ v => bytesOf v.val = bytesOf out.val ++ FramedChannel.Varint.encode n.val ⦄ := by
  unfold varint.encode_u32
  have hn : n.val < 2 ^ 32 := n.hBounds
  exact encode_loop_refines n out h ({ start := 0#i32, «end» := 5#i32 }, n, out)
    ⟨0, by omega, rfl, rfl, rfl, by simp only [Nat.sub_zero]; omega, by omega, rfl⟩

end FramedChannel.Bridge.varint

#print axioms FramedChannel.Bridge.varint.u32_and_127
#print axioms FramedChannel.Bridge.varint.u32_cast_u8_of_lt
#print axioms FramedChannel.Bridge.varint.u8_or_128
#print axioms FramedChannel.Bridge.varint.shiftRight_7
#print axioms FramedChannel.Bridge.varint.encode_loop_refines
#print axioms FramedChannel.Bridge.varint.encode_refines
