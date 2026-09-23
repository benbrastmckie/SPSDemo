-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.Crc8.Defs
import FramedChannel.Model.Crc8.Theorems

/-!
# Bridge/Crc8/Bitwise: the extracted bitwise `crc8` refines the model's `crc8Bits`

`[EXTRACTED: aeneas + bridge]` -- `crc8_refines` proves that the Charon/Aeneas extraction
of `rust/src/crc8.rs`'s `crc8` (`Extracted/Funs.lean`: an outer `loop` over the slice iterator and
an inner `loop` over the `i32` range `0..8`) returns, on every slice, the digest
`FramedChannel.Crc8.crc8Bits` (`lean/FramedChannel/Model/Crc8/Theorems.lean`) computes on its bytes, read
through `bitsOf`.

* `inner_loop_refines` / `inner_refines`: the inner loop is the model's `round`, eight `shift1`
  iterations. Its branch `crc & 0x80 != 0` is the model's `msb` test (`and_128_eq_zero_iff`, kernel
  `decide`), and each branch is one `shift1` (`shift1_of_msb`, `shift1_of_not_msb`). The `u8 << 1`
  shift wraps exactly as the model's `<<<` does and never fails (the amount is below 8).
* `outer_loop_refines`: after `i` bytes the running crc is the model's fold over the first `i`.
* `crc8_refines`: the extracted function from the empty iterator and seed `0`.

No SAT-backed decision procedure is used: every bit-vector fact here is kernel `decide` or
definitional. The triple is total correctness, so the extracted `crc8` never panics on any slice.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.crc8
open framed_channel
open FramedChannel.Crc8 (shift1)

/-- The branch the inner loop takes, as the model's `msb` test (kernel `decide`). -/
theorem and_128_eq_zero_iff (b : BitVec 8) : (b &&& 128#8 = 0#8) ↔ b.msb = false := by
  revert b
  decide

/-- One inner iteration with the top bit set is the model's `shift1`. -/
theorem shift1_of_msb (c : BitVec 8) (h : c.msb = true) :
    (c <<< 1) ^^^ crc8.POLY.bv = shift1 c := by
  unfold shift1 crc8.POLY
  simp only [h, if_true]
  rfl

/-- One inner iteration with the top bit clear is the model's `shift1`. -/
theorem shift1_of_not_msb (c : BitVec 8) (h : c.msb = false) : c <<< 1 = shift1 c := by
  unfold shift1
  simp only [h]
  rfl

/-- The inner loop invariant, over `(range, crc)`. -/
def InnerInv (k0 : Nat) (c0 : BitVec 8) (x : core.ops.range.Range Std.I32 × Std.U8) : Prop :=
  ∃ k : Nat, k0 ≤ k ∧ k ≤ 8 ∧ x.1.start.val = k ∧ x.1.end.val = 8 ∧
    shift1^[8 - k] x.2.bv = shift1^[8 - k0] c0

/-- The inner loop lemma: from any state satisfying `InnerInv`, the loop ends at `shift1` iterated
the remaining number of times. -/
theorem inner_loop_refines (k0 : Nat) (c0 : BitVec 8)
    (x : core.ops.range.Range Std.I32 × Std.U8) (hx : InnerInv k0 c0 x) :
    crc8.crc8_loop0_loop0 x.1 x.2 ⦃ c' => c'.bv = shift1^[8 - k0] c0 ⦄ := by
  unfold crc8.crc8_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (x : core.ops.range.Range Std.I32 × Std.U8) =>
      (x.1.end.val - x.1.start.val).toNat)
    (inv := InnerInv k0 c0)
  · rintro ⟨it, c⟩ ⟨k, hk0, hk8, hks, hke, heq⟩
    simp only at hks hke heq
    unfold crc8.crc8_loop0_loop0.body
    step*
    · have hk : k = 8 := by
        by_contra hne
        have hc : it.start.val < it.end.val := by omega
        simp only [hc, if_true] at o_post
        simp_all
      subst hk
      simpa using heq
    all_goals
      have hc : it.start.val < it.end.val := by
        by_contra hc
        simp only [hc, if_false] at o_post
        simp_all
      simp only [hc, if_true] at o_post
      obtain ⟨-, hstart⟩ := o_post
      have hk : k < 8 := by omega
      obtain ⟨f, hf⟩ : ∃ f, 8 - k = f + 1 := ⟨7 - k, by omega⟩
      rw [hf, Function.iterate_succ_apply] at heq
    · have hi : (i != 0#u8) = true := by assumption
      have hmsb : c.bv.msb = true := by
        cases hm : c.bv.msb
        · exfalso
          have h0 := (and_128_eq_zero_iff c.bv).mpr hm
          have : i = 0#u8 := by
            rw [UScalar.eq_equiv_bv_eq, i_post1]
            exact h0
          simp [this] at hi
        · rfl
      have hs : crc1.bv = shift1 c.bv := by
        rw [i1_post1] at crc1_post1
        exact crc1_post1.trans (shift1_of_msb c.bv hmsb)
      refine ⟨⟨k + 1, by omega, by omega, by rw [hstart, hks]; push_cast; rfl,
        by rw [o_post1]; exact hke, ?_⟩, by rw [hstart, o_post1]; omega⟩
      simp only
      rw [show 8 - (k + 1) = f by omega, hs]
      exact heq
    · have hi : ¬ (i != 0#u8) = true := by assumption
      have hmsb : c.bv.msb = false := by
        apply (and_128_eq_zero_iff c.bv).mp
        have : i = 0#u8 := UScalar.eq_of_val_eq (by simpa using hi)
        exact i_post1.symm.trans (by rw [this]; rfl)
      have hs : crc1.bv = shift1 c.bv := by
        exact crc1_post1.trans (shift1_of_not_msb c.bv hmsb)
      refine ⟨⟨k + 1, by omega, by omega, by rw [hstart, hks]; push_cast; rfl,
        by rw [o_post1]; exact hke, ?_⟩, by rw [hstart, o_post1]; omega⟩
      simp only
      rw [show 8 - (k + 1) = f by omega, hs]
      exact heq
  · exact hx

/-- The inner loop refines the model's eight-iteration `round`, and never fails.
`[EXTRACTED: aeneas + bridge]` -/
@[step]
theorem inner_refines (c : Std.U8) :
    crc8.crc8_loop0_loop0 { start := 0#i32, «end» := 8#i32 } c
      ⦃ c' => c'.bv = FramedChannel.Crc8.round c.bv ⦄ :=
  inner_loop_refines 0 c.bv ({ start := 0#i32, «end» := 8#i32 }, c)
    ⟨0, le_refl _, by omega, rfl, rfl, rfl⟩

/-- The outer loop invariant, over `(slice iterator, crc)`. -/
def OuterInv (s : Slice Std.U8) (x : core.slice.iter.Iter Std.U8 × Std.U8) : Prop :=
  x.1.slice = s ∧ x.1.i ≤ s.val.length ∧
    x.2.bv = ((bitsOf s.val).take x.1.i).foldl FramedChannel.Crc8.stepBits 0

/-- The outer loop lemma: from any state satisfying `OuterInv`, the loop ends at the model's digest
of the whole slice. -/
theorem outer_loop_refines (s : Slice Std.U8) (x : core.slice.iter.Iter Std.U8 × Std.U8)
    (hx : OuterInv s x) :
    crc8.crc8_loop0 x.1 x.2 ⦃ c => c.bv = FramedChannel.Crc8.crc8Bits (bitsOf s.val) ⦄ := by
  unfold crc8.crc8_loop0
  apply loop.spec_decr_nat
    (measure := fun (x : core.slice.iter.Iter Std.U8 × Std.U8) => s.val.length - x.1.i)
    (inv := OuterInv s)
  · rintro ⟨it, crc⟩ ⟨hsl, hi, heq⟩
    simp only at hsl hi heq
    subst hsl
    unfold crc8.crc8_loop0.body
    step*
    · have hon : o = none := by assumption
      rw [hon] at o_post
      have hge : it.slice.val.length ≤ it.i := List.getElem?_eq_none_iff.mp o_post.symm
      rw [heq, FramedChannel.Crc8.crc8Bits, List.take_of_length_le (by simp [bitsOf]; omega)]
    · have hob : o = some b := by assumption
      rw [hob] at o_post
      obtain ⟨hlt, hb⟩ := List.getElem?_eq_some_iff.mp o_post.symm
      simp only [hlt, if_true] at o_post2
      refine ⟨⟨o_post1, by simp only; omega, ?_⟩, by rw [o_post2]; omega⟩
      simp only
      have htake : (bitsOf it.slice.val).take (it.i + 1) =
          (bitsOf it.slice.val).take it.i ++ [b.bv] := by
        rw [List.take_add_one]
        simp [bitsOf, List.getElem?_map, List.getElem?_eq_getElem hlt, hb]
      rw [o_post2, htake, List.foldl_append, ← heq]
      exact crc2_post.trans (congrArg FramedChannel.Crc8.round crc1_post1)
  · exact hx

/-- Bitwise refinement: the extracted `crc8` never fails, and computes the model's bitwise CRC of
the slice's bytes. `[EXTRACTED: aeneas + bridge]` -/
theorem crc8_refines (s : Slice Std.U8) :
    crc8.crc8 s ⦃ c => c.bv = FramedChannel.Crc8.crc8Bits (bitsOf s.val) ⦄ := by
  unfold crc8.crc8
  step*
  exact outer_loop_refines s (iter, 0#u8) ⟨s_post, by simp only [iter_post]; omega, by simp only [iter_post]; rfl⟩

end FramedChannel.Bridge.crc8

#print axioms FramedChannel.Bridge.crc8.and_128_eq_zero_iff
#print axioms FramedChannel.Bridge.crc8.shift1_of_msb
#print axioms FramedChannel.Bridge.crc8.shift1_of_not_msb
#print axioms FramedChannel.Bridge.crc8.inner_loop_refines
#print axioms FramedChannel.Bridge.crc8.inner_refines
#print axioms FramedChannel.Bridge.crc8.outer_loop_refines
#print axioms FramedChannel.Bridge.crc8.crc8_refines
