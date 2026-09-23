-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.Varint.Encode

/-!
# Bridge/Varint/Decode: the extracted `decode_u32` loop refines the LEB128 model's `decode`

`[EXTRACTED: aeneas + bridge]` -- one loop lemma relating the Charon/Aeneas extraction of
`rust/src/varint.rs`'s `decode_u32` (`Extracted/Funs.lean`, a `loop` over the `usize` range `0..5`)
to `FramedChannel.Varint.decode` (`lean/FramedChannel/Model/Varint/Theorems.lean`), read through `bytesOf`.

## The relation, `DecPost`

The extracted decode is *stricter* than the model. The model decodes over `Nat` with no width
bound, so on a fifth byte `b < 128` it returns `acc + b * 128^4`, which is at least `2^32` exactly
when `b >= 16`; the Rust rejects that group (`group > 15` at shift 28) with `Err(Overlong)`. So the
relation is a case split on the extracted result, not an equality:

* `Ok((v, k))`: `k` is within the input, and the model succeeds with the same value, leaving
  `bytes[k..]`;
* `Err(_)`: the model fails, or it returns a value at or above `2^32`.

`Instance.lean` beside this file derives the three public decode theorems (success, completeness,
error agreement) and the round trip from `decode_refines` alone.

## The proof

`decode_loop_refines` is one application of `loop.spec_decr_nat` with measure `end - start` and
invariant `DecInv`: after `k` groups, `shift = 7k`, the accumulator is below `2^(7k)`, and the
model's whole decode equals `decodeF (5-k) (128^k) acc (bytes.drop k)`. Each branch of the body is
matched to one model step by `decode_ok_step` / `decode_cont_step`, and the machine arithmetic is
reduced to `Nat` by the lemmas below: or-as-add (`group_shift_or_eq`, because the accumulator fits
below the shift), no truncation of the `u32` shift (`no_trunc_lt` for shifts up to 21,
`no_trunc_last` for the last group, which the Rust bounds by 15), and the accumulator bound
(`acc_lt_after_step`). The `shift + 7` and `i + 1` obligations stay far below the machine bounds.
The triple is total correctness, so the extracted decode never panics or overflows, on any slice.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge.varint
open framed_channel

/-! ## Arithmetic: one decode step as `Nat` arithmetic -/

theorem u32_size_eq : U32.size = 2 ^ 32 := by
  simp only [U32.size_def]
  simp [U32.numBits]

theorem pow128_eq (k : Nat) : 128 ^ k = 2 ^ (7 * k) := by
  rw [Nat.pow_mul]

/-- The or-as-add step: shifting a group above an accumulator that fits below the shift adds. -/
theorem group_shift_or_eq (acc g j : Nat) (hacc : acc < 2 ^ j) (hno : g * 2 ^ j < 2 ^ 32) :
    acc ||| (g <<< j % 2 ^ 32) = acc + g * 2 ^ j := by
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hno, Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hacc, Nat.shiftLeft_eq, Nat.add_comm]

/-- The accumulator stays below the next shift. -/
theorem acc_lt_after_step (acc g k : Nat) (hacc : acc < 2 ^ (7 * k)) (hg : g < 128) :
    acc + g * 2 ^ (7 * k) < 2 ^ (7 * (k + 1)) := by
  have : 2 ^ (7 * (k + 1)) = 128 * 2 ^ (7 * k) := by
    rw [Nat.mul_succ, Nat.pow_add]; omega
  rw [this]
  have := Nat.mul_le_mul_right (2 ^ (7 * k)) (show g ≤ 127 by omega)
  omega

/-- No truncation: a seven-bit group shifted by at most 21 bits fits in 32 bits. -/
theorem no_trunc_lt (g k : Nat) (hg : g < 128) (hk : k ≤ 3) : g * 2 ^ (7 * k) < 2 ^ 32 := by
  have h1 : 2 ^ (7 * k) ≤ 2 ^ 21 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 := Nat.mul_le_mul (show g ≤ 127 by omega) h1
  omega

/-- No truncation at the last group: a group of at most four bits shifted by 28 fits in 32 bits. -/
theorem no_trunc_last (g : Nat) (hg : g ≤ 15) : g * 2 ^ (7 * 4) < 2 ^ 32 :=
  calc g * 2 ^ (7 * 4) ≤ 15 * 2 ^ (7 * 4) := Nat.mul_le_mul_right _ hg
    _ < 2 ^ 32 := by norm_num

theorem u8_and_127 (b : Std.U8) : (b &&& 127#u8).val = b.val % 128 := by
  rw [UScalar.val_and]
  exact Nat.and_two_pow_sub_one_eq_mod b.val 7

set_option maxRecDepth 10000 in
theorem u8_and_128_eq_zero (b : Std.U8) : (b &&& 128#u8) = 0#u8 ↔ b.val < 128 := by
  have key : ∀ x : Fin 256, (x.val &&& 128 = 0) ↔ x.val < 128 := by decide +kernel
  have hb : b.val < 256 := b.hBounds
  constructor
  · intro h
    have hv : (b &&& 128#u8).val = 0 := by rw [h]; rfl
    rw [UScalar.val_and] at hv
    exact (key ⟨b.val, hb⟩).mp hv
  · intro h
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    exact (key ⟨b.val, hb⟩).mpr h

theorem drop_bytesOf_some (l : List Std.U8) (k : Nat) (b : Std.U8) (h : l[k]? = some b) :
    (bytesOf l).drop k = b.val :: (bytesOf l).drop (k + 1) := by
  obtain ⟨hk, hb⟩ := List.getElem?_eq_some_iff.mp h
  have hk' : k < (bytesOf l).length := by simp [bytesOf, hk]
  rw [List.drop_eq_getElem_cons hk']
  simp [bytesOf, hb]

theorem drop_bytesOf_none (l : List Std.U8) (k : Nat) (h : l[k]? = none) :
    (bytesOf l).drop k = [] := by
  simp only [bytesOf, List.drop_eq_nil_iff, List.length_map]
  exact List.getElem?_eq_none_iff.mp h

theorem decodeF_lt (f m acc b : Nat) (rest : List Nat) (hb : b < 128) :
    FramedChannel.Varint.decodeF (f + 1) m acc (b :: rest) = .ok (acc + b * m, rest) := by
  simp [FramedChannel.Varint.decodeF, hb]

theorem decodeF_ge (f m acc b : Nat) (rest : List Nat) (hb : ¬ b < 128) :
    FramedChannel.Varint.decodeF (f + 1) m acc (b :: rest) =
      FramedChannel.Varint.decodeF f (m * 128) (acc + (b - 128) * m) rest := by
  simp [FramedChannel.Varint.decodeF, hb]

/-- A terminating group (below 128): the model returns the accumulated value. -/
theorem decode_ok_step (bs : List Nat) (acc g b k f : Nat) (rest : List Nat)
    (heq : FramedChannel.Varint.decode bs =
      FramedChannel.Varint.decodeF (f + 1) (128 ^ k) acc (b :: rest))
    (hb : b < 128) (hg : g = b % 128) :
    FramedChannel.Varint.decode bs = .ok (acc + g * 2 ^ (7 * k), rest) := by
  rw [heq, decodeF_lt _ _ _ _ _ hb, hg, Nat.mod_eq_of_lt hb, pow128_eq]

/-- A continuing group (at least 128): the model moves on with the group added. -/
theorem decode_cont_step (bs : List Nat) (acc g b k f : Nat) (rest : List Nat)
    (heq : FramedChannel.Varint.decode bs =
      FramedChannel.Varint.decodeF (f + 1) (128 ^ k) acc (b :: rest))
    (hb : ¬ b < 128) (hb256 : b < 256) (hg : g = b % 128) :
    FramedChannel.Varint.decode bs =
      FramedChannel.Varint.decodeF f (128 ^ (k + 1)) (acc + g * 2 ^ (7 * k)) rest := by
  have : b % 128 = b - 128 := by omega
  rw [heq, decodeF_ge _ _ _ _ _ hb, hg, this, ← pow128_eq, Nat.pow_succ]

/-- The machine accumulator after one group, as `Nat` addition. -/
theorem acc_step_val (acc1 acc g j : Nat) (hacc : acc < 2 ^ j) (hno : g * 2 ^ j < 2 ^ 32)
    (h : acc1 = acc ||| (g <<< j % U32.size)) : acc1 = acc + g * 2 ^ j := by
  rw [h, u32_size_eq, group_shift_or_eq acc g j hacc hno]

/-- The relation the decode loop establishes between the model's decode of `bs` and the
extracted result. -/
def DecPost (bs : List Nat) (r : core.result.Result (Std.U32 × Std.Usize) varint.VarintError) :
    Prop :=
  match r with
  | .Ok (v, k) => k.val ≤ bs.length ∧ FramedChannel.Varint.decode bs = .ok (v.val, bs.drop k.val)
  | .Err _ => FramedChannel.Varint.decode bs = .fail ∨
      ∃ n rest, FramedChannel.Varint.decode bs = .ok (n, rest) ∧ 2 ^ 32 ≤ n

/-- The decode loop invariant, over the loop state `(range, accumulator, shift)`. -/
def DecInv (s : Slice Std.U8)
    (x : core.ops.range.Range Std.Usize × Std.U32 × Std.U32) : Prop :=
  ∃ k : Nat, k ≤ 5 ∧ x.1.start.val = k ∧ x.1.end.val = 5 ∧ x.2.2.val = 7 * k ∧
    x.2.1.val < 2 ^ (7 * k) ∧
    FramedChannel.Varint.decode (bytesOf s.val) =
      FramedChannel.Varint.decodeF (5 - k) (128 ^ k) x.2.1.val ((bytesOf s.val).drop k)

/-- The decode loop lemma: from any state satisfying `DecInv`, the extracted loop's result is
related to the model's decode by `DecPost`. -/
theorem decode_loop_refines (s : Slice Std.U8)
    (x : core.ops.range.Range Std.Usize × Std.U32 × Std.U32) (hx : DecInv s x) :
    varint.decode_u32_loop x.1 s x.2.1 x.2.2 ⦃ r => DecPost (bytesOf s.val) r ⦄ := by
  unfold varint.decode_u32_loop
  apply loop.spec_decr_nat
    (measure := fun (x : core.ops.range.Range Std.Usize × Std.U32 × Std.U32) =>
      x.1.end.val - x.1.start.val)
    (inv := DecInv s)
  · rintro ⟨it, acc, sh⟩ ⟨k, hk5, hks, hke, hsh, hacc, heq⟩
    simp only at hks hke hsh hacc heq
    unfold varint.decode_u32_loop.body
    step*
    · -- the range is exhausted after five groups: the model's fuel is exhausted too
      have hk : k = 5 := by
        by_contra hne
        have hc : it.start.val < it.end.val := by omega
        simp only [hc, if_true] at o_post
        simp_all
      subst hk
      left
      rw [heq]
      rfl
    all_goals
      have hoi : o = some i := by assumption
      have hc : it.start.val < it.end.val := by
        by_contra hc
        simp only [hc, if_false] at o_post
        simp_all
      simp only [hc, if_true] at o_post
      obtain ⟨hio, hstart⟩ := o_post
      rw [hoi, Option.some.injEq] at hio
      have hk : k < 5 := by omega
      have hiv : i.val = k := by rw [hio]; exact hks
      obtain ⟨f, hf⟩ : ∃ f, 5 - k = f + 1 := ⟨4 - k, by omega⟩
      rw [hf] at heq
    · -- no byte at index k: the input is truncated, and the model runs out of input too
      have hon : o1 = none := by assumption
      rw [hon] at o1_post
      rw [drop_bytesOf_none s.val k (by rw [← hiv]; exact o1_post.symm)] at heq
      left
      rw [heq]
      rfl
    all_goals
      have hob : o1 = some b := by assumption
      rw [hob] at o1_post
      rw [drop_bytesOf_some s.val k b (by rw [← hiv]; exact o1_post.symm)] at heq
      have hg : group.val = b.val % 128 := by rw [group_post, i1_post, u8_and_127]
      have hb : b.val < 256 := b.hBounds
    · -- the fifth group is too wide for a u32: Overlong, and the model fails or overflows
      have hsh28 : sh = 28#u32 := by assumption
      have hgt : ¬ group.val ≤ 15 := by
        have : group > 15#u32 := by assumption
        scalar_tac
      have hk4 : k = 4 := by
        have : sh.val = 28 := by rw [hsh28]; rfl
        omega
      subst hk4
      by_cases hb128 : b.val < 128
      · right
        refine ⟨_, _, by rw [heq, decodeF_lt _ _ _ _ _ hb128], ?_⟩
        have : 16 * 128 ^ 4 ≤ b.val * 128 ^ 4 := Nat.mul_le_mul_right _ (by omega)
        norm_num at this ⊢
        omega
      · left
        have : f = 0 := by omega
        subst this
        rw [heq, decodeF_ge _ _ _ _ _ hb128]
        rfl
    · scalar_tac
    · -- the fifth group fits and ends the encoding: Ok, agreeing with the model
      have hsh28 : sh = 28#u32 := by assumption
      have hle : ¬ group > 15#u32 := by assumption
      have hle' : group.val ≤ 15 := by scalar_tac
      have hk4 : k = 4 := by
        have : sh.val = 28 := by rw [hsh28]; rfl
        omega
      subst hk4
      have hi3 : i3 = 0#u8 := by assumption
      have hb128 : b.val < 128 :=
        (u8_and_128_eq_zero b).mp (UScalar.eq_of_val_eq (by rw [← i3_post, hi3]))
      have hacc1 : acc1.val = acc.val + group.val * 2 ^ (7 * 4) :=
        acc_step_val _ _ _ _ hacc (no_trunc_last _ hle') (by rw [acc1_post, UScalar.val_or, i2_post])
      refine ⟨?_, ?_⟩
      · have hlt : i.val < s.val.length := (List.getElem?_eq_some_iff.mp o1_post.symm).1
        simp only [bytesOf, List.length_map]
        omega
      · rw [decode_ok_step _ _ _ _ _ _ _ heq hb128 hg, hacc1, i4_post, hiv]
    · -- the fifth group fits and continues: the next iteration finds the range exhausted
      have hsh28 : sh = 28#u32 := by assumption
      have hle : ¬ group > 15#u32 := by assumption
      have hle' : group.val ≤ 15 := by scalar_tac
      have hk4 : k = 4 := by
        have : sh.val = 28 := by rw [hsh28]; rfl
        omega
      subst hk4
      have hi3 : ¬ i3 = 0#u8 := by assumption
      have hb128 : ¬ b.val < 128 := fun hlt =>
        hi3 (UScalar.eq_of_val_eq (by rw [i3_post, (u8_and_128_eq_zero b).mpr hlt]))
      have hacc1 : acc1.val = acc.val + group.val * 2 ^ (7 * 4) :=
        acc_step_val _ _ _ _ hacc (no_trunc_last _ hle') (by rw [acc1_post, UScalar.val_or, i2_post])
      have hmodel := decode_cont_step _ _ _ _ _ _ _ heq hb128 hb hg
      refine ⟨⟨4 + 1, by omega, by rw [hstart, hks], by rw [o_post1]; exact hke,
        by rw [shift1_post], ?_, ?_⟩, ?_⟩
      · rw [hacc1]
        exact acc_lt_after_step _ _ _ hacc (by omega)
      · rw [hacc1, hmodel]
        have : f = 0 := by omega
        subst this
        rfl
      · rw [hstart, o_post1]
        omega
    · have hne : ¬ sh = 28#u32 := by assumption
      have : sh.val ≠ 28 := fun hv => hne (UScalar.eq_of_val_eq (by rw [hv]; rfl))
      omega
    · scalar_tac
    · -- a group below 28 bits ends the encoding: Ok, agreeing with the model
      have hne : ¬ sh = 28#u32 := by assumption
      have hk3 : k ≤ 3 := by
        have : sh.val ≠ 28 := fun hv => hne (UScalar.eq_of_val_eq (by rw [hv]; rfl))
        omega
      have hi3 : i3 = 0#u8 := by assumption
      have hb128 : b.val < 128 :=
        (u8_and_128_eq_zero b).mp (UScalar.eq_of_val_eq (by rw [← i3_post, hi3]))
      have hacc1 : acc1.val = acc.val + group.val * 2 ^ (7 * k) :=
        acc_step_val _ _ _ _ hacc (no_trunc_lt _ _ (by omega) hk3)
          (by rw [acc1_post, UScalar.val_or, i2_post, hsh])
      refine ⟨?_, ?_⟩
      · have hlt : i.val < s.val.length := (List.getElem?_eq_some_iff.mp o1_post.symm).1
        simp only [bytesOf, List.length_map]
        omega
      · rw [decode_ok_step _ _ _ _ _ _ _ heq hb128 hg, hacc1, i4_post, hiv]
    · -- a group below 28 bits continues
      have hne : ¬ sh = 28#u32 := by assumption
      have hk3 : k ≤ 3 := by
        have : sh.val ≠ 28 := fun hv => hne (UScalar.eq_of_val_eq (by rw [hv]; rfl))
        omega
      have hi3 : ¬ i3 = 0#u8 := by assumption
      have hb128 : ¬ b.val < 128 := fun hlt =>
        hi3 (UScalar.eq_of_val_eq (by rw [i3_post, (u8_and_128_eq_zero b).mpr hlt]))
      have hacc1 : acc1.val = acc.val + group.val * 2 ^ (7 * k) :=
        acc_step_val _ _ _ _ hacc (no_trunc_lt _ _ (by omega) hk3)
          (by rw [acc1_post, UScalar.val_or, i2_post, hsh])
      have hmodel := decode_cont_step _ _ _ _ _ _ _ heq hb128 hb hg
      refine ⟨⟨k + 1, by omega, by rw [hstart, hks], by rw [o_post1]; exact hke,
        by rw [shift1_post, hsh]; ring, ?_, ?_⟩, ?_⟩
      · rw [hacc1]
        exact acc_lt_after_step _ _ _ hacc (by omega)
      · rw [hacc1, hmodel]
        congr 1
        omega
      · rw [hstart, o_post1]
        omega
  · exact hx

/-- Decode refinement: the extracted `decode_u32` never fails, and its result is related to the
model's decode of the same bytes by `DecPost`. `[EXTRACTED: aeneas + bridge]` -/
theorem decode_refines (s : Slice Std.U8) :
    varint.decode_u32 s ⦃ r => DecPost (bytesOf s.val) r ⦄ := by
  unfold varint.decode_u32
  exact decode_loop_refines s ({ start := 0#usize, «end» := 5#usize }, 0#u32, 0#u32)
    ⟨0, by omega, rfl, rfl, rfl, by simp, rfl⟩

end FramedChannel.Bridge.varint

#print axioms FramedChannel.Bridge.varint.u32_size_eq
#print axioms FramedChannel.Bridge.varint.pow128_eq
#print axioms FramedChannel.Bridge.varint.group_shift_or_eq
#print axioms FramedChannel.Bridge.varint.acc_lt_after_step
#print axioms FramedChannel.Bridge.varint.no_trunc_lt
#print axioms FramedChannel.Bridge.varint.no_trunc_last
#print axioms FramedChannel.Bridge.varint.u8_and_127
#print axioms FramedChannel.Bridge.varint.u8_and_128_eq_zero
#print axioms FramedChannel.Bridge.varint.drop_bytesOf_some
#print axioms FramedChannel.Bridge.varint.drop_bytesOf_none
#print axioms FramedChannel.Bridge.varint.decodeF_lt
#print axioms FramedChannel.Bridge.varint.decodeF_ge
#print axioms FramedChannel.Bridge.varint.decode_ok_step
#print axioms FramedChannel.Bridge.varint.decode_cont_step
#print axioms FramedChannel.Bridge.varint.acc_step_val
#print axioms FramedChannel.Bridge.varint.decode_loop_refines
#print axioms FramedChannel.Bridge.varint.decode_refines
