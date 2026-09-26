-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Zigzag.Defs
import FramedChannel.Model.Zigzag.Theorems

/-!
# Bridge/Zigzag/Mapping: the extracted signed arithmetic is the model's zigzag map

`[EXTRACTED: aeneas + bridge]` -- the two scalar specifications this unit's refinement rests on.

`zigzag.zigzag` computes `(n << 1) ^ (n >> 31)` on `Std.I32`, where the extraction renders `>>` as
`BitVec.sshiftRight` -- an *arithmetic* shift, matching Rust's `>>` on a signed integer. The model
(`lean/FramedChannel/Model/Zigzag/Defs.lean`) states the same map arithmetically over `Int`:
`2 * n` on the non-negatives and `-2 * n - 1` on the negatives. `zz_bv` is the one genuinely new
lemma of this unit, and it is what ties the two spellings together, on every `BitVec 32`.

`zz_bv` is kernel-only. Its two `decide +kernel` sub-steps are closed bit-vector literal facts
(`BitVec.ofInt 32 (-1) = allOnes`, `BitVec.ofInt 32 0 = 0#32`); `bv_decide` is deliberately NOT
used, because it would add a compiler-trusting native helper axiom and so a new `flagged` row to
`certificate/policy.txt`. `i32_not_val` exists for the same reason: `simp [IScalar.val]` does not
see through `~~~x`, and the complement's value is obtained here from
`BitVec.toInt_eq_msb_cond` and `BitVec.toNat_not` instead.

`bmod_small` is the small arithmetic fact that `Int.bmod` is the identity on the non-negative half
of the `i32` range, which is what `UScalar.hcast .I32` needs on the `unzigzag` side.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.zigzag
open framed_channel

/-! ## Scalar facts -/

/-- `Int.bmod` at modulus `2 ^ 32` is the identity below `2 ^ 31`. -/
theorem bmod_small (a : Int) (h1 : 0 ≤ a) (h2 : a < 2 ^ 31) : Int.bmod a (2 ^ 32) = a := by
  rw [Int.bmod]; simp; omega

/-- The value of an `i32` bitwise complement, without `bv_decide`. -/
theorem i32_not_val (x : Std.I32) : (~~~x).val = -1 - x.val := by
  have h1 : (~~~x).bv = ~~~ x.bv := rfl
  have hlt : x.bv.toNat < 2 ^ 32 := x.bv.isLt
  show (~~~x.bv).toInt = -1 - x.bv.toInt
  rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond, BitVec.toNat_not]
  rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_not]
  simp only [decide_eq_true_eq]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  by_cases hm : 2 ^ 31 ≤ x.bv.toNat
  · rw [if_neg (by omega), if_pos (by omega)]; push_cast; omega
  · rw [if_pos (by omega), if_neg (by omega)]; push_cast; omega

/-- The bit-vector form of the zigzag map equals the model's arithmetic form, on every
`BitVec 32`. Kernel-only: the two `decide +kernel` steps are closed literal facts, and no
`bv_decide` appears. -/
theorem zz_bv (b : BitVec 32) :
    ((b <<< (1:Nat)) ^^^ (b.sshiftRight 31)).toNat
      = if 0 ≤ b.toInt then (2 * b.toInt).toNat else (-2 * b.toInt - 1).toNat := by
  have hlt : b.toNat < 2 ^ 32 := b.isLt
  have hsl : b.toNat <<< (1:Nat) = b.toNat * 2 := by simp [Nat.shiftLeft_eq]
  by_cases hm : b.msb = true
  · have hge : 2 ^ 31 ≤ b.toNat := by
      have := BitVec.msb_eq_decide b; simp only [hm] at this; simp at this; omega
    have hti : b.toInt = (b.toNat : Int) - 2 ^ 32 := by
      rw [BitVec.toInt_eq_msb_cond, if_pos hm]; push_cast; ring
    have hs : b.sshiftRight 31 = BitVec.allOnes 32 := by
      rw [BitVec.sshiftRight_eq]
      have h1 : b.toInt >>> (31:Nat) = -1 := by
        rw [Int.shiftRight_eq_div_pow, hti]; push_cast; omega
      rw [h1]; decide +kernel
    rw [hs, BitVec.xor_allOnes, BitVec.toNat_not, BitVec.toNat_shiftLeft, hsl,
      if_neg (by omega : ¬ (0 ≤ b.toInt))]
    have hmod : b.toNat * 2 % 2 ^ 32 = b.toNat * 2 - 2 ^ 32 := by
      have h2 : b.toNat * 2 < 2 * 2 ^ 32 := by omega
      have h3 : 2 ^ 32 ≤ b.toNat * 2 := by omega
      omega
    rw [hmod, hti]; push_cast; omega
  · have hm' : b.msb = false := by simpa using hm
    have hlt31 : b.toNat < 2 ^ 31 := by
      have := BitVec.msb_eq_decide b; simp only [hm'] at this; simp at this; omega
    have hti : b.toInt = (b.toNat : Int) := by rw [BitVec.toInt_eq_msb_cond, hm']; simp
    have hs : b.sshiftRight 31 = 0#32 := by
      rw [BitVec.sshiftRight_eq]
      have h1 : b.toInt >>> (31:Nat) = 0 := by
        rw [Int.shiftRight_eq_div_pow, hti]; push_cast; omega
      rw [h1]; decide +kernel
    rw [hs, BitVec.xor_zero, BitVec.toNat_shiftLeft, hsl,
      if_pos (by omega : (0:Int) ≤ b.toInt)]
    have hmod : b.toNat * 2 % 2 ^ 32 = b.toNat * 2 := Nat.mod_eq_of_lt (by omega)
    rw [hmod, hti]; omega

/-! ## The two specifications -/

/-- The extracted `zigzag` is the model's `zigzag`, on every machine `i32`.
`[EXTRACTED: aeneas + bridge]` -/
theorem zigzag_spec (n : Std.I32) :
    zigzag.zigzag n ⦃ v => v.val = FramedChannel.Zigzag.zigzag n.val ⦄ := by
  unfold zigzag.zigzag
  step*
  have hbv : i2.bv = (n.bv <<< (1:Nat)) ^^^ (n.bv.sshiftRight 31) := by
    simp only [i2_post1, i_post1, i1_post1]
  have hval : (IScalar.hcast .U32 i2).val = i2.bv.toNat :=
    congrArg BitVec.toNat (BitVec.signExtend_eq i2.bv)
  rw [hval, hbv, zz_bv]
  show _ = FramedChannel.Zigzag.zigzag n.bv.toInt
  unfold FramedChannel.Zigzag.zigzag
  rfl

/-- The extracted `unzigzag` is the model's `unzigzag`, on every machine `u32`.
`[EXTRACTED: aeneas + bridge]` -/
theorem unzigzag_spec (m : Std.U32) :
    zigzag.unzigzag m ⦃ v => v.val = FramedChannel.Zigzag.unzigzag m.val ⦄ := by
  unfold zigzag.unzigzag
  have hm : m.val < 2 ^ 32 := m.hBounds
  step* <;> rename_i hcase
  · have he : m.val % 2 = 0 := by
      have h0 : (m &&& 1#u32).val = 0 := by rw [← i1_post, hcase]; rfl
      rw [UScalar.val_and] at h0
      simpa [Nat.and_one_is_mod] using h0
    have hi : i.val = m.val / 2 := by rw [i_post]; simp [Nat.shiftRight_eq_div_pow]
    rw [half_post, UScalar.hcast_val_eq, hi]
    unfold FramedChannel.Zigzag.unzigzag
    rw [if_pos he]
    exact bmod_small _ (by omega) (by omega)
  · have ho : m.val % 2 = 1 := by
      have h0 : (m &&& 1#u32).val ≠ 0 := by
        intro h0; exact hcase (UScalar.eq_of_val_eq (by rw [i1_post]; simpa using h0))
      rw [UScalar.val_and] at h0
      have h1 : m.val % 2 ≠ 0 := by simpa [Nat.and_one_is_mod] using h0
      omega
    have hi : i.val = m.val / 2 := by rw [i_post]; simp [Nat.shiftRight_eq_div_pow]
    rw [i32_not_val, half_post, UScalar.hcast_val_eq, hi]
    unfold FramedChannel.Zigzag.unzigzag
    rw [if_neg (by omega)]
    simp only [IScalarTy.numBits]
    rw [bmod_small _ (by omega) (by omega)]
    omega

end FramedChannel.Bridge.zigzag

#print axioms FramedChannel.Bridge.zigzag.bmod_small
#print axioms FramedChannel.Bridge.zigzag.i32_not_val
#print axioms FramedChannel.Bridge.zigzag.zz_bv
#print axioms FramedChannel.Bridge.zigzag.zigzag_spec
#print axioms FramedChannel.Bridge.zigzag.unzigzag_spec
