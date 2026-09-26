-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs

/-!
# Bridge/Std: step specifications the pinned Aeneas library does not provide

`[HAND-WRITTEN]` -- `@[step]` lemmas about Aeneas's own library models, proved here because
the pinned library (`nix/aeneas-pin.json`) has no specification for them, so `step*` stops at each call:

* `range_i32_next_spec`: `IteratorRange.next` over `StepI32`. The Rust `for _ in 0..5` and
  `for _ in 0..8` loops iterate over `i32`, and the library only specifies the unsigned ranges.
  The postcondition is conditional, in the shape of the library's own
  `IteratorRange.next_UScalar_spec`.
* `slice_get_usize_spec`: `Slice.get` at `SliceIndexUsizeSlice`, as the list's optional index.
* `slice_iter_next_spec`: `IteratorSliceIter.next`, the `for b in bytes` iterator.
* `from_u32_u8_spec`: `u32::from(u8)`, which the extraction emits as a `lift`ed pure function
  with no step specification.

The channel's frame codec (`Bridge/Channel/`) needs four more:

* `vec_extend_from_slice_spec`: `Vec::extend_from_slice` under an identity `Clone`, with the
  `Usize.max` bound on the result as its one hypothesis (the library panics beyond it).
* `slice_get_range_from_spec` and `slice_get_range_to_spec`: `Slice.get` at `RangeFrom` and
  `RangeTo`, the `rest.get(used..)` and `body.get(..n)` of `parse_frame` and `drop_front`.
* `usize_saturating_sub_spec`: `usize::saturating_sub`, `deliver`'s in-flight decrement.

Each is a theorem about a library *definition*, not an assumption. None of them uses, or may use,
the library's `@[step]` axiom `core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec`: nothing
in the crate calls `get_unchecked`, and the axiom audit would reject any record that reached it.

Only the component bridges that walk loops, and the channel bridge, import this module; the ring
buffer's refinement does not, so these specifications cannot change what `step*` does there.

## Why this module stays flat

Every other module under `Bridge/` lives in a `Bridge/<Unit>/` directory, one directory per unit,
and that is the rule (`aeneas/README.md`). This module is the one exception, deliberately: it is
not a unit. It holds package-level library-gap `@[step]` specifications about *Aeneas's own*
library definitions, shared by the Varint, Crc8 and Channel bridges and owned by none of them, so
there is no unit directory it could belong to. A flat module directly under a unit layer means
package-level infrastructure, and `Bridge/Std.lean` is its only instance.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge

/-- `IteratorRange.next` over an `i32` range: below the end it yields the start and advances by
one; otherwise it yields `none` and leaves the start. Never fails. -/
@[step]
theorem range_i32_next_spec (r : core.ops.range.Range Std.I32) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 r
      ⦃ o r' => (if r.start.val < r.end.val then o = some r.start ∧ r'.start.val = r.start.val + 1
                 else o = none ∧ r'.start = r.start) ∧ r'.end = r.end ⦄ := by
  unfold core.iter.range.IteratorRange.next
  simp [core.iter.range.StepI32, core.iter.range.IScalarStep,
    core.iter.range.IScalarStep.forward_checked]
  by_cases hlt : r.start.val < r.end.val
  · have hle : r.start.val + 1 ≤ I32.max := by scalar_tac
    simp [core.cmp.impls.PartialOrdI32.lt, hlt, hle]
  · simp [core.cmp.impls.PartialOrdI32.lt, hlt]

/-- `Slice.get` at a `usize` index is the list's optional index. Never fails. -/
@[step]
theorem slice_get_usize_spec {T : Type} (s : Slice T) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T) s i
      ⦃ o => o = s.val[i.val]? ⦄ := by
  simp [core.slice.Slice.get, core.slice.index.Usize.get]

/-- `IteratorSliceIter.next`: yields the element at the cursor and advances it while the cursor is
inside the slice; otherwise yields `none`. The slice itself never changes. Never fails. -/
@[step]
theorem slice_iter_next_spec {T : Type} (it : core.slice.iter.Iter T) :
    core.slice.iter.IteratorSliceIter.next it
      ⦃ o it' => o = it.slice.val[it.i]? ∧ it'.slice = it.slice ∧
        it'.i = (if it.i < it.slice.val.length then it.i + 1 else it.i) ⦄ := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · rename_i h
    have h' : it.i < it.slice.val.length := by simpa [Slice.len_val] using h
    simp only [h', List.getElem?_eq_getElem h', if_true, WP.spec_ok]
    exact ⟨rfl, rfl, rfl⟩
  · rename_i h
    have h' : ¬ it.i < it.slice.val.length := by simpa [Slice.len_val] using h
    simp [h']

/-- `u32::from(u8)`: the `lift`ed pure widening keeps the value. Never fails. -/
@[step]
theorem from_u32_u8_spec (x : Std.U8) :
    lift (core.convert.num.FromU32U8.from x) ⦃ y => y.val = x.val ⦄ := by
  simp only [lift, WP.spec_ok]
  exact core.convert.num.FromU32U8.from_val_eq x

/-- `Vec::extend_from_slice` under an identity `Clone` appends the slice. Fails only when the
result would exceed `Usize.max`, which the hypothesis rules out. -/
@[step]
theorem vec_extend_from_slice_spec {T : Type} (cloneInst : core.clone.Clone T)
    (hcl : ∀ x, cloneInst.clone x = ok x) (v : alloc.vec.Vec T) (s : Slice T)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice cloneInst v s ⦃ v' => v'.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  have h' : v.length + s.length ≤ Usize.max := by simpa using h
  rw [dif_pos h']
  have hc := Slice.clone_spec (clone := cloneInst.clone) (s := s) (fun x _ => hcl x)
  obtain ⟨s', hs, heq⟩ := (WP.spec_equiv_exists _ _).mp hc
  subst heq
  split
  · rename_i s'' h''
    rw [hs] at h''
    simp at h''
    subst h''
    simp
  · rename_i h''
    rw [hs] at h''; simp at h''
  · rename_i h''
    rw [hs] at h''; simp at h''

/-- `Slice.get` at a `RangeFrom` (`&s[start..]` as `get`): the suffix when `start` is within the
slice, else `none`. Never fails. -/
@[step]
theorem slice_get_range_from_spec {T : Type} (s : Slice T) (r : core.ops.range.RangeFrom Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexRangeFromUsizeSlice T) s r
      ⦃ o => o = if r.start.val ≤ s.val.length then some (s.drop r.start) else none ⦄ := by
  simp [core.slice.Slice.get, core.slice.index.SliceIndexRangeFromUsizeSlice.get]
  split <;> simp_all

/-- `Slice.get` at a `RangeTo` (`&s[..end]` as `get`): the prefix of length `end` when it fits,
else `none`. Never fails. -/
@[step]
theorem slice_get_range_to_spec {T : Type} (s : Slice T) (r : core.ops.range.RangeTo Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice T) s r
      ⦃ o => (r.end.val ≤ s.val.length → ∃ s', o = some s' ∧ s'.val = s.val.take r.end.val) ∧
             (s.val.length < r.end.val → o = none) ⦄ := by
  simp [core.slice.Slice.get, core.slice.index.SliceIndexRangeToUsizeSlice.get]
  split <;> simp_all

/-- `usize::saturating_sub` is truncated subtraction on the values. Never fails. -/
@[step]
theorem usize_saturating_sub_spec (x y : Usize) :
    lift (core.num.Usize.saturating_sub x y) ⦃ z => z.val = x.val - y.val ⦄ := by
  simp [lift, core.num.Usize.saturating_sub, UScalar.saturating_sub]
  have hx : x.val < 2 ^ System.Platform.numBits := by
    have := x.hBounds; simpa [UScalarTy.numBits] using this
  simp only [UScalar.val]
  exact Nat.mod_eq_of_lt (by simp only [UScalar.val] at hx; omega)

/-- `usize::saturating_add` is addition capped at `Usize.max`. Never fails.

Reached from `rust/src/receiver.rs`'s `finish_run`, whose `dropped.saturating_add(1)` is what leaves
`feed`'s refinement triple with no arithmetic hypothesis at all: a plain `+= 1` would be an addition
Aeneas models as a panic on overflow, and every triple would then carry `dropped < usize::MAX`. The
mirror of `usize_saturating_sub_spec` above, which `stuffed_channel.rs`'s `in_flight.saturating_sub(1)`
reaches for the same reason. -/
@[step]
theorem usize_saturating_add_spec (x y : Usize) :
    lift (core.num.Usize.saturating_add x y)
      ⦃ z => z.val = min (UScalar.max UScalarTy.Usize) (x.val + y.val) ⦄ := by
  simp [lift, core.num.Usize.saturating_add, UScalar.saturating_add]
  have hmax : UScalar.max UScalarTy.Usize < 2 ^ System.Platform.numBits := by
    rw [UScalar.max]
    have h0 : (0 : Nat) < 2 ^ (UScalarTy.Usize).numBits := Nat.two_pow_pos _
    simp [UScalarTy.numBits] at h0 ⊢
  simp only [UScalar.val]
  exact Nat.mod_eq_of_lt (by omega)

end FramedChannel.Bridge

#print axioms FramedChannel.Bridge.range_i32_next_spec
#print axioms FramedChannel.Bridge.slice_get_usize_spec
#print axioms FramedChannel.Bridge.slice_iter_next_spec
#print axioms FramedChannel.Bridge.from_u32_u8_spec
#print axioms FramedChannel.Bridge.vec_extend_from_slice_spec
#print axioms FramedChannel.Bridge.slice_get_range_from_spec
#print axioms FramedChannel.Bridge.slice_get_range_to_spec
#print axioms FramedChannel.Bridge.usize_saturating_sub_spec
#print axioms FramedChannel.Bridge.usize_saturating_add_spec
