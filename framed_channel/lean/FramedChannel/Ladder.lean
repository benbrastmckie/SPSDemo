-- SPDX-License-Identifier: Apache-2.0
import Lean
import Std.Tactic.BVDecide

/-!
# Ladder: the proof-method ladder, recorded where each theorem is declared

## What this module is

Tooling, like `Certify.lean`: it declares no theorem about the example. It gives the proof
modules three things.

* `rung <method> => <tactics>`, a tactic. It runs `<tactics>` as the proof, so the proof term is
  exactly the one the unwrapped script produces. Before that it checks two things and fails the
  build if either is false:
  1. **the label matches the script** (the syntax-class check below): a `simp` record must be one
     simp call, a `retrieval` record must name a library theorem, and so on;
  2. **no strictly cheaper rung closes the same goal** (the audit below).
  It then logs one line `ladder <declaration> <method>`, which `check.sh` collects from the build
  log into `certificate/ladder.txt`, the same pipeline as the `#print axioms` records.
* `ladder_record% <ident> <method>`, a command, for the few registered declarations that cannot
  be wrapped: the shared-proof pair `RingBuffer.push_inv`/`pop_inv`, whose proofs live in a
  definitions module that the approved specification imports (wrapping them would change the
  approved digests), and the class instances (method `instance`).
* `refuted% <candidate> <false_thm> <search_thm>`, a command recording a rejected candidate
  statement together with the kernel-checked witness that refutes it
  (`Evidence/Countermodels.lean`).

## The rungs, in cost order

`decide < simp < omega < grind < retrieval < bv_decide < manual`

| Rung        | What the script may be                                                     |
|-------------|-----------------------------------------------------------------------------|
| `decide`    | `decide`                                                                    |
| `simp`      | one `simp`/`simp_all`/`simpa`/`dsimp` call naming no theorem                |
| `omega`     | `omega`                                                                     |
| `grind`     | an optional `simp`/`unfold` naming no theorem, then one `grind` naming none |
| `retrieval` | `exact <theorem> ...`, or an optional such preparation step then one simp or grind call naming at least one theorem |
| `bv_decide` | an optional preparation step naming no theorem, then `bv_decide`. **Compiler-trusting**: its record carries a native helper axiom, so the row is flagged in `certificate/policy.txt` |
| `manual`    | anything                                                                    |

"Naming a theorem" is decided by resolving each identifier in the script: a global constant
whose type is a proposition is a theorem; a definition, a simproc or a local hypothesis is not.
A definition hint only unfolds what the statement already says, so it keeps a script on the
automatic rungs; a theorem hint is a premise someone found, which is what retrieval means.

`manual` means a script a person or an outside agent wrote. The gate cannot tell which, and does
not claim to: this is the same stance as the approvals. **There is deliberately no AI-prover
rung** and no extension point for one. An external prover's output is a script like any other and
can only be recorded by the rung its syntax falls into; no AI prover is demonstrated by this
repository.

## The audit

Before the inner script runs, each rung strictly cheaper than the label is tried on the same goal,
inside `saveState`/`restore`, with one fixed canonical tactic per rung:

| Rung        | Canonical attempt                                                           |
|-------------|------------------------------------------------------------------------------|
| `decide`    | revert every hypothesis, then `decide`                                      |
| `simp`      | `simp_all [hints]`                                                          |
| `omega`     | `omega`                                                                     |
| `grind`     | `grind [hints]`, else `(try simp only [hints] at *); grind`                 |
| `retrieval` | `exact?`                                                                    |
| `bv_decide` | `(try simp only [hints] at *); bv_decide`                                   |

The hint set is mechanical, never hand-picked: every definition of the `FramedChannel` namespace
that the goal or a hypothesis mentions, closed transitively over those definitions' bodies (at
most `maxHints` names), excluding instances, projections, matchers and type formers, each as a
fully qualified identifier (a short `Inv` would be ambiguous with `_root_.Inv`).

Four details, each found by experiment, make the audit sound:

* **It runs where the theorem is declared.** A probe of the finished environment is unsound:
  `exact?` there finds the theorem itself, or a later duplicate of it. Inside the proof, the
  theorem does not exist yet.
* **The theorem's own auxiliary local is cleared first.** Inside a `by` block the local context
  carries the declaration being elaborated (for recursion), and `grind` will happily close the
  goal through it.
* **A rung counts as closing only if** no goal remains, the instantiated term contains no
  metavariable and no `sorry` (explicit or synthetic), neither directly nor inside an auxiliary
  constant the attempt created (`grind` wraps its proof in one), and the attempt logged no new
  error. `exact?` and
  `grind? +suggestions` can "succeed" with a `sorry` and only a warning.
* **Each attempt has a fixed heartbeat budget** (`auditHeartbeats`), run under
  `withCurrHeartbeats` and caught with `tryCatchRuntimeEx`: heartbeat and recursion-depth
  exceptions are runtime exceptions that an ordinary `try`/`catch` does not see. Heartbeats are
  deterministic; there is no wall-clock timeout, so the audit gives the same verdict on every
  machine.

The qualifier `(excluding bv_decide)` marks a row that exists to be kernel-only
(`Crc8.crc8_step_linear_kernel`, the kernel replay of the one `bv_decide` row). Its audit skips
the `bv_decide` rung, and a cheaper closer whose term rests on a compiler-trusting axiom does not
count: `exact?` there finds the `bv_decide` row itself, which would close the goal by exactly
the trust the row exists to avoid. The record carries the qualifier.

The retrieval audit runs only inside `rung`: `ladder_record%` runs after the declaration exists,
where `exact?` would find it, so it runs the other rungs only and says so in the record.

## Toolchain drift

The audit's verdicts belong to the pinned toolchain (`lean-toolchain`), like the statement hashes.
A newer `simp` or `grind` may close a goal recorded as `manual` or `retrieval`; the build then
fails naming the cheaper rung. That is the intended signal: rewrite the proof to the cheaper
method and let the record follow.
-/

namespace FramedChannel.Ladder

open Lean Elab Tactic Meta Term Command

/-! ## Methods -/

/-- The proof methods, in cost order. There is no AI-prover constructor: see the module doc. -/
inductive Method where
  | decide
  | simp
  | omega
  | grind
  | retrieval
  | bv_decide
  | manual
  deriving DecidableEq, Repr, Inhabited

namespace Method

/-- Every method, cheapest first. -/
def all : List Method := [.decide, .simp, .omega, .grind, .retrieval, .bv_decide, .manual]

/-- Position in the cost order. -/
def rank : Method → Nat
  | .decide => 0
  | .simp => 1
  | .omega => 2
  | .grind => 3
  | .retrieval => 4
  | .bv_decide => 5
  | .manual => 6

/-- The name written in source and in the record. -/
def label : Method → String
  | .decide => "decide"
  | .simp => "simp"
  | .omega => "omega"
  | .grind => "grind"
  | .retrieval => "retrieval"
  | .bv_decide => "bv_decide"
  | .manual => "manual"

def ofLabel? (s : String) : Option Method := all.find? (·.label == s)

end Method

/-- The heartbeat budget of one audit attempt, in thousands (the unit of `maxHeartbeats`). -/
def auditHeartbeats : Nat := 20000

/-- The largest hint set the audit builds. -/
def maxHints : Nat := 48

/-! ## Syntax -/

/-- A method name. Non-reserved, so `manual` and `retrieval` stay usable as identifiers. -/
syntax ladderMethod := &"decide" <|> &"simp" <|> &"omega" <|> &"grind" <|> &"retrieval" <|>
  &"bv_decide" <|> &"manual"

/-- The one qualifier: the row is deliberately kernel-only. The `bv_decide` rung is not audited,
and no cheaper closer counts if its term rests on a compiler-trusting axiom (for instance
retrieving the `bv_decide` row it replays). -/
syntax ladderQualifier := "(" &"excluding" &"bv_decide" ")"

/-- `rung <method> [(excluding bv_decide)] => <tactics>`: see the module doc. -/
syntax (name := rungTac) "rung " ladderMethod (ppSpace ladderQualifier)? " => " tacticSeq : tactic

/-- The method a `ladderMethod` node names. -/
def methodOf (stx : Syntax) : Except String Method := do
  let some atom := stx.find? fun s => s.isAtom || s.isIdent
    | throw "ladder: malformed method"
  let s := if atom.isIdent then atom.getId.toString else atom.getAtomVal
  match Method.ofLabel? s with
  | some m => pure m
  | none => throw s!"ladder: unknown method '{s}'"

/-! ## The syntax-class check -/

/-- The tactics of a tactic sequence, in order. -/
def seqTactics (seq : Syntax) : Array Syntax :=
  let inner := seq[0]
  if inner.getKind == ``Lean.Parser.Tactic.tacticSeqBracketed then inner[1].getSepArgs
  else inner[0].getSepArgs

def simpKinds : Array SyntaxNodeKind :=
  #[``Lean.Parser.Tactic.simp, ``Lean.Parser.Tactic.simpAll, ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.dsimp]

/-- Every identifier occurring in a syntax tree. -/
partial def identsOf (stx : Syntax) : Array Syntax :=
  if stx.isIdent then #[stx] else stx.getArgs.foldl (fun acc a => acc ++ identsOf a) #[]

/-- Is `c` a theorem, in the sense of the ladder: a constant whose type is a proposition. -/
def isTheoremConst (c : Name) : MetaM Bool := do
  let info ← getConstInfo c
  isProp info.type

/-- The global theorems an identifier list names. Local hypotheses shadow globals and are not
theorems; identifiers that do not resolve (simp-set names, locations) are not theorems. -/
def namedTheorems (ids : Array Syntax) : TacticM (Array Name) := do
  let lctx ← getLCtx
  let mut out := #[]
  for id in ids do
    if (lctx.findFromUserName? id.getId).isSome then continue
    let cs ← try realizeGlobalConst id catch _ => pure []
    for c in cs do
      if ← isTheoremConst c then out := out.push c
  return out

/-- A preparation step: a simp-family call or `unfold`, naming no theorem. -/
def isPrepStep (tac : Syntax) : TacticM Bool := do
  if !(simpKinds.contains tac.getKind || tac.getKind == ``Lean.Parser.Tactic.unfold) then
    return false
  return (← namedTheorems (identsOf tac)).isEmpty

/-- The head identifier of an application term. -/
partial def headIdent? (t : Syntax) : Option Syntax :=
  if t.isIdent then some t
  else if t.getKind == ``Lean.Parser.Term.app then headIdent? t[0]
  else if t.getKind == ``Lean.Parser.Term.explicit then headIdent? t[1]
  else if t.getKind == ``Lean.Parser.Term.paren then headIdent? t[1]
  else none

/-- Fail unless the script `seq` is in the syntax class of `m` (see the module doc's table). -/
def checkClass (m : Method) (seq : Syntax) : TacticM Unit := do
  let tacs := seqTactics seq
  let kind (i : Nat) : SyntaxNodeKind := tacs[i]!.getKind
  let thms (i : Nat) : TacticM (Array Name) := namedTheorems (identsOf tacs[i]!)
  let ok ← match m with
    | .manual => pure true
    | .decide => pure (tacs.size == 1 && kind 0 == ``Lean.Parser.Tactic.decide)
    | .omega => pure (tacs.size == 1 && kind 0 == ``Lean.Parser.Tactic.omega)
    | .simp => do
      pure (tacs.size == 1 && simpKinds.contains (kind 0) && (← thms 0).isEmpty)
    | .grind => do
      let last := tacs.size - 1
      if tacs.size == 0 || tacs.size > 2 then pure false
      else if kind last != ``Lean.Parser.Tactic.grind then pure false
      else if !(← thms last).isEmpty then pure false
      else if tacs.size == 2 then isPrepStep tacs[0]!
      else pure true
    | .bv_decide => do
      let last := tacs.size - 1
      if tacs.size == 0 || tacs.size > 2 then pure false
      else if kind last != ``Lean.Parser.Tactic.bvDecide then pure false
      else if tacs.size == 2 then isPrepStep tacs[0]!
      else pure true
    | .retrieval => do
      if tacs.size == 1 && kind 0 == ``Lean.Parser.Tactic.exact then
        match headIdent? tacs[0]![1] with
        | none => pure false
        | some h => pure !(← namedTheorems #[h]).isEmpty
      else
        let last := tacs.size - 1
        if tacs.size == 0 || tacs.size > 2 then pure false
        else if !(simpKinds.contains (kind last) || kind last == ``Lean.Parser.Tactic.grind) then
          pure false
        else if (← thms last).isEmpty then pure false
        else if tacs.size == 2 then isPrepStep tacs[0]!
        else pure true
  unless ok do
    throwError "ladder: the script is not in the syntax class of the '{m.label}' rung (see \
      the rung table in FramedChannel/Ladder.lean)"

/-! ## The audit -/

/-- Is `c` a definition the audit may unfold: in the `FramedChannel` namespace, a plain
definition (not an instance, projection, matcher or internal detail) whose type is not a type
former. Predicates such as `Inv` are kept. -/
def isHintable (c : Name) : MetaM Bool := do
  unless (`FramedChannel).isPrefixOf c do return false
  if c.isInternalDetail then return false
  let env ← getEnv
  let some (.defnInfo info) := env.find? c | return false
  if isInstanceCore env c then return false
  if (← isProjectionFn c) then return false
  if (isMatcherCore env c) then return false
  if (`FramedChannel.Ladder).isPrefixOf c || (`FramedChannel.Certify).isPrefixOf c then
    return false
  if ← isProp info.type then return false
  forallTelescopeReducing info.type fun _ body => do
    match (← whnf body) with
    | .sort u => return u.isZero
    | _ => return true

/-- The mechanical hint set of a goal: see the module doc. -/
def hintsOf (g : MVarId) : MetaM (Array Name) := g.withContext do
  let mut roots : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      roots := roots.push (← instantiateMVars d.type)
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut work : Array Name := roots.foldl (fun acc e => acc ++ e.getUsedConstants) #[]
  while !work.isEmpty && out.size < maxHints do
    let c := work.back!
    work := work.pop
    if seen.contains c then continue
    seen := seen.insert c
    if ← isHintable c then
      out := out.push c
      if let some (.defnInfo info) := (← getEnv).find? c then
        work := work ++ info.value.getUsedConstants
  return out.qsort (·.toString < ·.toString)

/-- The canonical attempt of one rung (never `manual`). -/
def canonical (r : Method) (hints : Array Name) : TacticM Unit := do
  let ids : Array Ident := hints.map mkIdent
  let simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    ids.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  let grindArgs : Array (TSyntax ``Lean.Parser.Tactic.grindParam) ←
    ids.mapM fun i => `(Lean.Parser.Tactic.grindParam| $i:ident)
  match r with
  | .decide =>
    liftMetaTactic fun g => do
      let fvars := (← g.getDecl).lctx.foldl (init := #[]) fun acc d =>
        if d.isImplementationDetail then acc else acc.push d.fvarId
      let (_, g) ← g.revert fvars (preserveOrder := true)
      return [g]
    evalTactic (← `(tactic| decide))
  | .simp =>
    if ids.isEmpty then evalTactic (← `(tactic| simp_all))
    else evalTactic (← `(tactic| simp_all [$simpArgs,*]))
  | .omega => evalTactic (← `(tactic| omega))
  | .grind =>
    if ids.isEmpty then evalTactic (← `(tactic| grind))
    else evalTactic (← `(tactic| first
      | grind [$grindArgs,*]
      | ((try simp only [$simpArgs,*] at *); grind)))
  | .retrieval => evalTactic (← `(tactic| exact?))
  | .bv_decide =>
    if ids.isEmpty then evalTactic (← `(tactic| bv_decide))
    else evalTactic (← `(tactic| ((try simp only [$simpArgs,*] at *); bv_decide)))
  | .manual => throwError "ladder: manual has no canonical attempt"

def errorCount : CoreM Nat := do
  return (← getThe Core.State).messages.toList.foldl
    (fun n msg => if msg.severity matches .error then n + 1 else n) 0

/-- Does the term `e` carry a `sorry`, directly or through a constant created after `env0`?
Tactics such as `grind` wrap their proof in an auxiliary lemma, so the term alone can look clean
while the lemma it names was closed with `sorry`. -/
def carriesSorry (env0 : Environment) (e : Expr) : MetaM Bool := do
  if e.hasSorry || e.hasSyntheticSorry then return true
  let mut seen : NameSet := {}
  let mut work := e.getUsedConstants
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    if seen.contains c || env0.contains c then continue
    seen := seen.insert c
    let some info := (← getEnv).find? c | continue
    let exprs := [info.type] ++ (match info with
      | .thmInfo t => [t.value]
      | .defnInfo d => [d.value]
      | _ => [])
    for x in exprs do
      if x.hasSorry || x.hasSyntheticSorry then return true
      work := work ++ x.getUsedConstants
  return false

/-- A compiler-trusting axiom: `Lean.ofReduceBool`, `Lean.trustCompiler`, or a native
`bv_decide` helper axiom (`<declaration>._native.bv_decide.ax_<n>_<m>`). -/
def isCompilerTrusting (ax : Name) : Bool :=
  ax == ``Lean.ofReduceBool || ax == ``Lean.trustCompiler ||
    ax.components.any (· == `_native)

/-- Does the term `e` rest on a compiler-trusting axiom? -/
def restsOnCompiler (e : Expr) : MetaM Bool := do
  for c in e.getUsedConstants do
    if (← collectAxioms c).any isCompilerTrusting then return true
  return false

/-- Does rung `r` close goal `g`? With `kernelOnly`, a closer whose term rests on a
compiler-trusting axiom does not count. Always restores the state; never throws. -/
def closes (g : MVarId) (r : Method) (hints : Array Name) (kernelOnly := false) :
    TacticM Bool := do
  let s ← saveState
  let env0 ← getEnv
  let errs0 ← errorCount
  let closed ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := auditHeartbeats * 1000 })
      (withCurrHeartbeats do
        setGoals [g]
        canonical r hints
        let open_ ← getUnsolvedGoals
        let e ← instantiateMVars (mkMVar g)
        return open_.isEmpty && !e.hasExprMVar && !(← carriesSorry env0 e) &&
          (← errorCount) == errs0 && !(kernelOnly && (← restsOnCompiler e))))
    (fun _ => pure false)
  s.restore (restoreInfo := true)
  return closed

/-- The goal with the declaration's own auxiliary local (and any other) cleared. -/
def clearAux (g : MVarId) : MetaM MVarId := do
  let auxs := (← g.getDecl).lctx.foldl (init := #[]) fun acc d =>
    if d.isAuxDecl then acc.push d.fvarId else acc
  g.tryClearMany auxs

/-- Fail if a rung strictly cheaper than `m` closes `g`. `skip` lists rungs not to audit. -/
def audit (declName : Name) (g : MVarId) (m : Method) (skip : List Method) : TacticM Unit := do
  let s ← saveState
  let g' ← clearAux g
  let hints ← hintsOf g'
  let mut closer : Option Method := none
  for r in Method.all do
    if closer.isNone && r.rank < m.rank && !skip.contains r then
      if ← closes g' r hints (kernelOnly := skip.contains .bv_decide) then closer := some r
  -- clearing the auxiliary local assigned `g`; the proof itself runs on the untouched goal
  s.restore (restoreInfo := true)
  if let some r := closer then
        throwError "ladder: {declName} is labelled {m.label}, but the cheaper rung {r.label} \
          closes it (canonical attempt with hints {hints.toList}); rewrite the proof with the \
          cheaper method"

@[tactic rungTac] def evalRung : Tactic := fun stx => do
  let m ← match methodOf stx[1] with
    | .ok m => pure m
    | .error e => throwError e
  let excluding := !stx[2].isNone
  if excluding && m.rank ≤ Method.bv_decide.rank then
    throwError "ladder: '(excluding bv_decide)' only qualifies a rung above bv_decide"
  let seq := stx[4]
  let some declName ← Term.getDeclName?
    | throwError "ladder: rung must be the proof of a named declaration"
  let goals ← getGoals
  unless goals.length == 1 do
    throwError "ladder: rung must be applied to exactly one goal, the declaration's statement"
  let g ← getMainGoal
  checkClass m seq
  audit declName g m (if excluding then [.bv_decide] else [])
  setGoals [g]
  evalTactic seq
  let qual := if excluding then " (excluding bv_decide)" else ""
  logInfo m!"ladder {declName} {m.label}{qual}"

/-! ## Post-declaration records -/

syntax ladderRecordMethod := ladderMethod <|> &"instance"

/-- `ladder_record% <ident> <method>`: see the module doc. -/
syntax (name := ladderRecordCmd) "ladder_record% " ident ppSpace ladderRecordMethod : command

@[command_elab ladderRecordCmd] def elabLadderRecord : CommandElab := fun stx => do
  let id := stx[1]
  let mstx := stx[2]
  let isInst := (mstx.find? fun s => (s.isAtom || s.isIdent) &&
    (s.isAtom && s.getAtomVal == "instance" || s.isIdent && s.getId == `instance)).isSome
  liftTermElabM do
    let c ← realizeGlobalConstNoOverload id
    let info ← getConstInfo c
    if isInst then
      unless isInstanceCore (← getEnv) c do
        throwError "ladder: {c} is recorded as an instance but is not one"
      logInfo m!"ladder {c} instance"
      return
    let m ← match methodOf mstx with
      | .ok m => pure m
      | .error e => throwError e
    unless info matches .thmInfo _ do
      throwError "ladder: {c} is not a theorem; ladder_record% records theorems and instances"
    let mvar ← mkFreshExprMVar info.type (kind := .syntheticOpaque)
    let (_, g) ← mvar.mvarId!.intros
    let hints ← hintsOf g
    for r in Method.all do
      if r.rank < m.rank && r != .retrieval then
        let result ← IO.mkRef false
        let _ ← Tactic.run g (do result.set (← closes g r hints))
        if ← result.get then
          throwError "ladder: {c} is labelled {m.label}, but the cheaper rung {r.label} closes \
            it (canonical attempt with hints {hints.toList}); rewrite the proof with the cheaper \
            method"
    logInfo m!"ladder {c} {m.label} (post-declaration; retrieval audit not run)"

/-! ## Refuted candidates -/

/-- `refuted% <candidate> <false_thm> <search_thm>`: see the module doc. -/
syntax (name := refutedCmd) "refuted% " ident ppSpace ident ppSpace ident : command

@[command_elab refutedCmd] def elabRefuted : CommandElab := fun stx => do
  liftTermElabM do
    let cand ← realizeGlobalConstNoOverload stx[1]
    let falseThm ← realizeGlobalConstNoOverload stx[2]
    let searchThm ← realizeGlobalConstNoOverload stx[3]
    let candInfo ← getConstInfo cand
    unless candInfo matches .defnInfo _ do
      throwError "refuted%: {cand} must be a definition of the candidate proposition"
    unless candInfo.type.isProp do
      throwError "refuted%: {cand} must have type Prop"
    let fInfo ← getConstInfo falseThm
    unless fInfo matches .thmInfo _ do
      throwError "refuted%: {falseThm} must be a theorem"
    unless fInfo.type == mkApp (mkConst ``Not) (mkConst cand) do
      throwError "refuted%: {falseThm} must state exactly ¬ {cand}, but states{indentExpr fInfo.type}"
    let sInfo ← getConstInfo searchThm
    unless sInfo matches .thmInfo _ do
      throwError "refuted%: {searchThm} must be a theorem"
    let some (_, _, rhs) := sInfo.type.eq?
      | throwError "refuted%: {searchThm} must state a search result `_ = some w`"
    unless rhs.isAppOfArity ``Option.some 2 do
      throwError "refuted%: {searchThm} must state a search result `_ = some w`"
    let w ← whnf rhs.appArg!
    logInfo m!"countermodel {cand} {w}"

end FramedChannel.Ladder
