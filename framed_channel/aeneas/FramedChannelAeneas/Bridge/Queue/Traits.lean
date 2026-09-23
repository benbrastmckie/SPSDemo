-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Bridge.Queue.Defs

/-!
# Bridge/Queue/Traits: the trait-record assumptions every component bridge shares

`[HAND-WRITTEN]` -- the one place the bridge layer says what it assumes about the trait records
the extraction threads through every function.

The Rust is generic over `T: Default + Clone`, so every extracted function takes a
`core.default.Default T` and a `core.clone.Clone T` record. The bridge theorems quantify over
**any** `Default` record and over any `Clone` record whose `clone` returns its argument unchanged
(`CloneIsId`). `Default` needs no hypothesis: the extracted ring-buffer `get` consults it only on
an out-of-range index, which the model's `Inv` rules out. `Clone`-is-identity holds for `u32` and
for the derived `Clone` of `Vec<u8>` frames (proved below as `cloneVecU8_isId`), but it is an
assumption about the instance, not something proved about arbitrary `Clone` impls. The canonical
records `dflt` and `cln` and the predicate `CloneIsId` are defined in `Bridge/Queue/Defs.lean`;
`cln_isId` below shows `cln` satisfies it.

These are component-independent, so they live here rather than in any one component's bridge.
-/

open Aeneas Aeneas.Std Result

namespace FramedChannel.Bridge

variable {α : Type}

/-- The canonical `Clone` record satisfies the assumption, so it is not vacuous. -/
theorem cln_isId : CloneIsId (cln (α := α)) := fun _ => rfl

/-- The `Clone` record the extraction actually uses for frames, the derived `Clone` of `Vec<u8>`
(`CloneallocvecVec` over `CloneU8`), satisfies the assumption. This is proved, so no bridge theorem
about a queue of frames carries `CloneIsId` as a hypothesis. `[PROVED: kernel]` -/
theorem cloneVecU8_isId : CloneIsId (core.clone.CloneallocvecVec core.clone.CloneU8) := by
  intro v
  obtain ⟨s', hs, heq⟩ := (WP.spec_equiv_exists _ _).mp
    (Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := v.slice) (by intro x _; rfl))
  subst heq
  show alloc.vec.CloneVec.clone core.clone.CloneU8 v = ok v
  simp [alloc.vec.CloneVec.clone, hs]

end FramedChannel.Bridge

#print axioms FramedChannel.Bridge.cln_isId
#print axioms FramedChannel.Bridge.cloneVecU8_isId
