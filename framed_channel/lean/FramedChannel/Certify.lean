-- SPDX-License-Identifier: Apache-2.0
import Lean

/-!
# Certify: the scoring bank and its identifier-driven registration

## Provenance

A minimal, self-contained version of a scoring-bank vocabulary used elsewhere: the `name_of%`
elaborator, `CertifiedItem`, `register%` and `toBank`, plus the `ItemType`/`Status`/`Item`
metadata and the tier-scaled scoring functions. Only what `Registry.lean` needs is included (no
constructors for unsettled rows); `stmt_hash%` and `register%`'s hash argument are specific to
this repository (see "Statement-hash binding" below).

## What the registration macro buys

A scoring row identifies the theorem it certifies. A hand-typed *string* would link that row to
nothing: it could be misspelled, renamed, or name a constant that does not exist, and the bank
would still build and score. `register%` drives registration by a Lean **identifier** and splices
the same identifier into both the derived name string (`name_of% $thm`) and the proof
(`cert := PLift.up @$thm`), so the two provably refer to one constant and the kernel
type-checks the proof against the carried statement at bank elaboration.

The proof is spliced as `@$thm`, with explicit-argument elaboration, so `Stmt` is inferred as the
constant's full type whatever its binder style. A plain `$thm` would instantiate leading implicit
and instance binders with metavariables that nothing solves, so a theorem written with
`{α : Type}` (every bridge theorem, and model lemmas such as `RingBuffer.pushBQ_ok`) could not be
registered. The statement hash is unaffected: `stmt_hash_check%` hashes the constant's declared
type, not the elaborated `cert` term.

## Scope of the guarantee

The linkage is enforced on the **construction path** only. A row built through `register%` cannot
name a theorem that is absent or whose statement differs from the spliced proof's type. Full
reflective enforcement of `item.name = nameOf cert` inside the type is not expressible in Lean,
because a proof term's type does not carry its own constant name. The `verified` flag is an
independent, externally supplied verdict (this repository's axiom audit, `check.sh`), not
something this module checks.
-/

namespace FramedChannel.Certify

open Lean Elab Term Meta

/-! ## The bank metadata and its scoring -/

/-- The seven eval item types. This example uses `E1` and `E2`; the rest are carried so that the
vocabulary stays complete. -/
inductive ItemType
  /-- per-axiom soundness unit -/
  | E1
  /-- definability witness -/
  | E2
  /-- non-definability certificate -/
  | E3
  /-- distribution / extraction rewrite lemma -/
  | E4
  /-- termination measure and well-foundedness -/
  | E5
  /-- metatheorem -/
  | E6
  /-- capstone, decomposed into a lemma DAG -/
  | E7
  deriving DecidableEq, Repr

/-- Item status. An `open` item is a flagged frontier target: maximum weight, never scored as
settled, permitted a permanent sorry. This example registers only `settled` rows. -/
inductive Status
  /-- proved sorry-free, clean axioms -/
  | settled
  /-- a scoped division point: partial DAG credit only -/
  | declaredSorry
  /-- a frontier target: never scores as settled -/
  | «open»
  deriving DecidableEq, Repr

/-- A bank item: a fixed statement (identified by `name`) with its scoring metadata.
`dagTotal`/`dagDone` support lemma-DAG partial credit; `verified` records the external audit's
verdict; `witness` names the nonvacuity instance. -/
structure Item where
  name      : String
  itemType  : ItemType
  tier      : Nat
  status    : Status
  verified  : Bool := false
  dagTotal  : Nat := 1
  dagDone   : Nat := 0
  witness   : String := ""
  deriving Repr

namespace Item

/-- Tier-scaled base weight: higher tiers are worth more. An `open` (frontier) item is maximum
weight so the harness rewards genuine frontier progress most; it is never actually scored. -/
def baseWeight (it : Item) : Nat :=
  match it.status with
  | Status.«open» => 100
  | _ => it.tier + 1

/-- Partial-credit score: the full `baseWeight` if passed, else a DAG-proportional share for a
declared-sorry capstone, and always `0` for an `open` item. -/
def score (it : Item) : Nat :=
  match it.status with
  | Status.«open» => 0
  | Status.settled => if it.verified then it.baseWeight else 0
  | Status.declaredSorry => it.baseWeight * it.dagDone / it.dagTotal

/-- The maximum achievable settled score for an item. An `open` item contributes `0` by design. -/
def maxScore (it : Item) : Nat :=
  match it.status with
  | Status.«open» => 0
  | _ => it.baseWeight

/-- A row is nonvacuously guarded iff it names a witness string. -/
def hasWitness (it : Item) : Bool := it.witness ≠ ""

end Item

/-- Total achieved score over a bank. -/
def totalScore (bank : List Item) : Nat := (bank.map Item.score).foldl (· + ·) 0

/-- Total achievable settled score over a bank. -/
def totalMax (bank : List Item) : Nat := (bank.map Item.maxScore).foldl (· + ·) 0

/-- Anti-gaming invariant, machine-checkable over a concrete bank: no `open` item is ever
scored. -/
def noOpenScored (bank : List Item) : Prop :=
  ∀ it ∈ bank, it.status = Status.«open» → it.score = 0

/-- The invariant holds for every bank, unconditionally: `score` returns `0` on `open` by
construction. `[PROVED: kernel]` -/
theorem noOpenScored_all (bank : List Item) : noOpenScored bank := by
  intro it _ hopen
  simp only [Item.score, hopen]

/-! ## Identifier-driven registration -/

/-- Resolve an identifier to its fully-qualified name as a `String` literal. Elaboration
**error** if the constant does not exist: a row naming a nonexistent theorem cannot be
constructed. -/
elab "name_of%" thm:ident : term => do
  let cst ← realizeGlobalConstNoOverload thm
  return mkStrLit (toString cst)

/-! ### Statement-hash binding

`name_of%` stops a row from naming a constant that is absent. It does nothing about a constant
that still exists but whose *statement* has been weakened: add a vacuous hypothesis to a
registered theorem and the name still resolves, the proof still type-checks against its own now
weaker type, and the row keeps its trust flag.

`stmt_hash% thm` closes that by evaluating to the structural hash of the resolved constant's
elaborated type. `register%` carries that number as a row field and compares it at elaboration
against the identifier's actual hash, so weakening a registered theorem changes its type, hence
its hash, and fails the build with a drift error naming both numbers.

Scope: the hash is `Lean.Expr`'s own `hash`, a 64-bit structural digest reduced to a
`Nat`. It is a *change detector*, not a cryptographic commitment -- a deliberate collision is not
ruled out. It is also toolchain-sensitive, which is why `lean-toolchain` is pinned and why the
drift error names the refresh command rather than asking anyone to retype a literal. -/

/-- The structural hash of the resolved constant's elaborated statement, as a `Nat` literal.
Used to generate the hash column of `Registry.lean`'s rows; see `scripts/refresh-hashes.sh`. -/
elab "stmt_hash%" thm:ident : term => do
  let cst ← realizeGlobalConstNoOverload thm
  let info ← getConstInfo cst
  return mkNatLit (hash info.type).toNat

/-- A scoring row PLUS the certificate linking it to the theorem it certifies. `item` is the
scoring metadata; `Stmt` is the certified theorem's statement; `cert` is a proof of `Stmt`.
`item.name` is derived from the same constant as `cert`, so the string cannot drift from the
proved theorem, and `item.stmtHash` pins that constant's elaborated statement.

Construct via `register%` only. -/
structure CertifiedItem where
  item : Item
  /-- The structural hash of `Stmt` as elaborated at registration time. -/
  stmtHash : Nat
  Stmt : Prop
  cert : PLift Stmt

/-- Check, at elaboration, that `thm`'s current statement still hashes to `expected`. -/
def checkStmtHash (thmName : Name) (expected actual : Nat) : MetaM Unit := do
  if expected != actual then
    throwError "\
registry statement drift: '{thmName}' was registered against statement hash {expected}, \
but its statement now elaborates to hash {actual}.

The theorem's statement changed after the row was written, so the row no longer certifies what \
it claims. Either restore the statement, or -- if the change is intended -- regenerate every \
row's hash with

    bash scripts/refresh-hashes.sh    (from the framed_channel/ directory)

and re-read the rows before committing."

/-- Elaborate `stmt_hash_check% thm expected` to `expected`, failing if `thm`'s statement no
longer hashes to it. `expected` is a bare numeric literal because the hash column is
machine-generated (`scripts/refresh-hashes.sh`): admitting an arbitrary term there would let an
expression compute whatever the row needed. -/
elab "stmt_hash_check%" thm:ident expected:num : term => do
  let cst ← realizeGlobalConstNoOverload thm
  let info ← getConstInfo cst
  checkStmtHash cst expected.getNat (hash info.type).toNat
  return mkNatLit expected.getNat

/-- Register a **settled** row BY IDENTIFIER (never by string). The same `$thm` is spliced into
the derived name string, the statement-hash check and the proof, so the name, the pinned statement
and the proof refer to one constant by construction. `Stmt := _` is inferred as the theorem's
actual type, so the kernel checks `cert : Stmt` at bank elaboration.

Arguments: `thm` (identifier), `ty` (`ItemType`), `tier` (`Nat`), `v` (`verified : Bool`),
`h` (the pinned statement hash, a numeric literal generated by `scripts/refresh-hashes.sh`),
`w` (`witness : String`). -/
macro "register%" thm:ident ty:term:max tier:term:max v:term:max h:num w:term:max : term =>
  `({ item := { name := name_of% $thm, itemType := $ty, tier := $tier,
                status := Status.settled, verified := $v, witness := $w },
      stmtHash := stmt_hash_check% $thm $h,
      Stmt := _, cert := PLift.up @$thm : CertifiedItem })

/-- Recover the `List Item` the scoring functions consume. -/
def toBank (rows : List CertifiedItem) : List Item := rows.map (·.item)

#print axioms noOpenScored_all

end FramedChannel.Certify
