-- SPDX-License-Identifier: Apache-2.0
/-
HAND-WRITTEN, NOT GENERATED. The crate's trusted library models, crate-local.

The generated `Funs.lean` imports this module: it supplies the five library functions the
framed_channel crate calls but the pinned Aeneas Lean library does not model. Each is a
definition with a proved `@[step]` spec (except `from_residual`, whose only residual is `None`),
mirroring the shape of Aeneas's own models (`Result`'s `Try`/`FromResidual`, `Vec.new`,
`Slice.split_at`).

Trust: a spec proves a property of the Lean definition. That the definition models the Rust
function named in its `rust_fun` attribute is trusted, exactly as Aeneas's own library models are.
Each definition therefore carries a one-line citation of the Rust semantics it follows.

This file holds proved definitions only: no axiom declarations, no proof holes or admitted goals,
and no compiler-trusting decision procedures. `scripts/refresh-extraction.sh` and `check.sh` scan for all
of them, and `scripts/refresh-extraction.sh` checks that its `rust_fun` names are exactly those in the
template Aeneas emits, so a new external (or one an Aeneas bump now models) fails the extraction
by name.
-/
import Aeneas
import FramedChannelAeneas.Extracted.Types
open Aeneas Aeneas.Std Result ControlFlow Error
open framed_channel

/-- Rust `<Option<T> as Try>::branch` (the `?` operator): `Some(v)` continues with `v`, `None`
breaks with the residual `None`. The residual's payload type is Rust's never type `!`, which the
pinned Aeneas/Charon revision models as `Aeneas.Std.Never`, an empty inductive; the `rust_fun`
name pattern itself names the same empty type `!`. -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} :
  Option T → Result (core.ops.control_flow.ControlFlow (Option Never) T)
  | some v => ok (.Continue v)
  | none => ok (.Break none)

/-- Rust `<Option<T> as FromResidual<Option<!>>>::from_residual`: the residual `None` returns
`None`; `Some` of the never type `Aeneas.Std.Never` is uninhabited. -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual"]
def
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
  (T : Type) : Option Never → Result (Option T)
  | none => ok none
  | some x => nomatch x

/-- Rust `<[T]>::split_first`: `None` on an empty slice, else `Some((first, rest))`. Never
panics. -/
@[rust_fun "core::slice::{[@T]}::split_first"]
def core.slice.Slice.split_first
  {T : Type} (s : Slice T) : Result (Option (T × (Slice T))) :=
  match h : s.val with
  | [] => ok none
  | x :: xs => ok (some (x, Slice.from xs (by have := s.property; simp [h] at this; omega)))

/-- Rust `Vec::remove`: removes and returns the element at `index`, shifting the rest left;
panics when `index >= len`. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
def alloc.vec.Vec.remove
  {T : Type} (_A : Type) (v : alloc.vec.Vec T) (i : Std.Usize) :
  Result (T × (alloc.vec.Vec T)) :=
  if h : i.val < v.length then
    ok (v.val[i.val], alloc.vec.Vec.from (v.val.eraseIdx i.val)
      (by have h1 := v.property; rw [List.length_eraseIdx]; split <;> omega))
  else fail .panic

/-- Rust `<Vec<T> as Default>::default`: the empty vector, as `Vec::new`. -/
@[rust_fun
  "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.Vec.Insts.CoreDefaultDefault.default
  (T : Type) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

@[step]
theorem core.option.Option.Insts.CoreOpsTry_traitTry.branch.spec {T : Type} (o : Option T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    ⦃ cf => cf = match o with | some v => .Continue v | none => .Break none ⦄ := by
  cases o <;> simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch]

@[step]
theorem core.slice.Slice.split_first.spec {T : Type} (s : Slice T) :
    core.slice.Slice.split_first s
    ⦃ r => (r.map fun p => (p.1, p.2.val)) = (match s.val with
            | [] => none | x :: xs => some (x, xs)) ⦄ := by
  unfold core.slice.Slice.split_first
  split <;> simp_all

@[step]
theorem alloc.vec.Vec.remove.spec {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Std.Usize)
    (h : i.val < v.length) :
    alloc.vec.Vec.remove A v i ⦃ x v' => x = v.val[i.val] ∧ v'.val = v.val.eraseIdx i.val ⦄ := by
  simp [alloc.vec.Vec.remove, h]

@[step]
theorem alloc.vec.Vec.Insts.CoreDefaultDefault.default.spec (T : Type) :
    alloc.vec.Vec.Insts.CoreDefaultDefault.default T ⦃ v => v.val = [] ⦄ := by
  simp [alloc.vec.Vec.Insts.CoreDefaultDefault.default]
