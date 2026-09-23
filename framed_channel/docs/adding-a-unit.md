# Adding a unit to `framed_channel`

This procedure adds **a protocol-scoped unit of the `framed_channel` worked example** — a new
Rust module, Lean model, bridge, certificate manifest and gate coverage for something that is
plausibly part of the framed-channel protocol itself (for example, a second checksum variant, or
a piece of the receive path). It is not the procedure for adding a component unrelated to this
example: the gate, its helper scripts and its single certificate identity are all scoped to
`framed_channel/` and are not parameterized by a top-level project directory. Follow this
document only when the unit belongs to `framed_channel`'s own story.

**This procedure has been executed once by hand, end to end**, against a deliberately small
protocol-scoped XOR-8 checksum unit, on a throwaway branch, with the full gate passing
(`check.sh: PASS`) at the end of the run. Every defect that execution found — a missing `open
framed_channel` at step 9, an imprecise "re-export" phrasing at step 1, and several other
clarifications — is fixed in the text below, not merely recorded elsewhere.

## Before you start

**Dev shells.** `nix develop .#<name>` selects one; see
[`../../docs/installation.md`](../../docs/installation.md)'s dev-shell table for the full
definitions. The steps below name one per step:

| Shell | What it adds over a plain `nix develop` |
|---|---|
| `default` (light — what a plain `nix develop` gives you) | lint + build toolchains only: Rust, elan, jq, perl, git |
| `extraction` | `default` plus the prebuilt charon/aeneas — needed for anything that runs charon (extraction, candidate refresh) |
| `recheck` | `default` plus comparator, landrun and prebuilt charon/aeneas — the independent-recheck stage only |
| `build` | the pinned Rust toolchain, elan, jq, perl, git (a named alias of what `default` carries) |
| `lint` | shellcheck, actionlint, git |

Steps 1-7 below (the core half) only ever need the light `default` shell. Once you reach step 8
(extraction), the whole remainder of the sequence — steps 8 through 15 — can be run without
leaving `.#extraction`; it is the simplest single shell to stay in from there on, since it is a
superset of what every later step needs except the recheck-only stage.

**SPDX headers.** `scripts/check-spdx.sh` (run by the gate) requires
`SPDX-License-Identifier: Apache-2.0` in the **first three lines** of every hand-written `.rs`
and `.lean` file this procedure creates. Add it before anything else in each new file — the exact
line matches the first line of any existing module, e.g. `framed_channel/rust/src/crc8.rs` or
`framed_channel/lean/FramedChannel/Model/Crc8/Defs.lean`.

## Step 1 — Rust module

**Where**: `framed_channel/rust/src/<unit>.rs` (one file per unit, named for the unit's Rust
type — `framed_channel/README.md`'s forward rule), plus `pub mod <unit>;` in
`framed_channel/rust/src/lib.rs`. **"Re-export" means re-export any newly public *type*
(`channel.rs`/`queue.rs`/`ring_buffer.rs`'s pattern) — a function-only unit like `crc8.rs` or
`varint.rs` needs only the `pub mod` line; there is no top-level `pub use` for either, and
callers reach the functions through `framed_channel::<unit>::<fn>` (see
`rust/tests/differential.rs`'s own imports).**

**Dev shell**: `default` (light).

Stay inside the Rust subset (`framed_channel/rust/README.md`'s "The Rust subset"):
`#![forbid(unsafe_code)]`; no interior mutability (`Cell`, `RefCell`, `Mutex`, `Arc`); no trait
objects, closures or iterator chains (generics with trait bounds are fine — `BoundedQueue<T>` is
the example); no `unwrap`/`expect` in `src/`; every slice/array read through `get`, never an
indexing expression that can panic; every loop bounded.

**Commands**:

```bash
cargo fmt
cargo clippy
cargo test
bash ../scripts/check-spdx.sh   # from rust/, or run from the repo root against the new file
```

## Step 2 — Spec interface (only if new)

**Where**: `framed_channel/lean/FramedChannel/Spec/<Interface>.lean` — an L0 operations record
plus an L1 laws class.

**Dev shell**: `default` (light); `lake build` inside `lean/`, no network.

Only write a new interface if the unit's operation shape does not already fit one of the four
that exist: `QueueModel`, `CodecModel`, `ChecksumModel`, plus `Result`. Read
`lean/FramedChannel/Spec/` before assuming a new interface is needed — reusing an existing one is
the common case, and the recipe step is a check, not a default write.

## Step 3 — Model

**Where**: `framed_channel/lean/FramedChannel/Model/<X>/Defs.lean` (representation, invariant if
any, operations, interface instance) and `.../Theorems.lean` (error agreement, invariant
preservation where applicable, refinement, bounds). Close every declaration with `#print axioms`.
Both files carry the SPDX header.

**All four of those Theorems.lean categories may be vacuous** for a sufficiently simple unit —
for example, a fold-only checksum with no table and no partial operation (no error case, no
invariant, no separate bounds theorem), where "refinement" collapses to the interface instance
itself (the model satisfying the abstract class's laws) and that instance is the *only* proof
obligation the unit owes. This is expected, not a gap to fill: check an existing manifest's
`coverage:` block (e.g. `certificate/crc8.yaml`) for which categories a similar unit claims
versus marks "not claimed" before assuming a theorem is missing.

**Dev shell**: `default` (light).

## Step 4a — Registry rows (core half)

**Where**: `framed_channel/lean/FramedChannel/Registry.lean`.

**Dev shell**: `default` (light); `refresh-hashes.sh` needs only the pinned Lean toolchain.

Add rows for the newly registered core theorems with a `0` hash (a placeholder the refresh script
fills in). Before editing the file's tail, **read the current `bank.length` / `totalScore bank` /
`totalMax bank` values from its `example : ... := by decide` statements — never copy a number
from any document, including this one; both totals change with every unit added, and are already
stale by the time you read them here.** Update those `decide` statements to the post-addition
values, then run:

```bash
bash scripts/refresh-hashes.sh --core-only
```

`refresh-hashes.sh`'s own header states the ordering: the core registry must be current **before**
the bridge registry (step 10), which imports it. Never run `--aeneas` before `--core-only` when
both need refreshing.

## Step 5 — Challenge module (core half)

**Where**: `framed_channel/lean/FramedChannelChallenge/<X>.lean` (new), and the root
`FramedChannelChallenge.lean` (add the import).

**Dev shell**: `default` (light).

Restate each newly registered core theorem `:= sorry`, importing only `Defs`/specification
modules — never the proof modules themselves.

## Step 6 — Select and approve (core-only)

**Dev shell**: `.#extraction` only for the charon-backed `refresh-candidates.sh` run below; the
approval commands themselves need only what `default` provides plus `git`/`column`.

```bash
bash scripts/refresh-candidates.sh                       # if rust/src changed; needs charon
bash approve.sh --review --selection --core-only --out FILE
# edit FILE, mark items reviewed
bash approve.sh --record FILE --approver "..." --core-only
```

If step 8's extraction refresh is coming soon anyway, it is fine to defer `refresh-candidates.sh`
and run it once alongside step 8's `refresh-extraction.sh`, rather than entering `.#extraction`
twice — also because a not-yet-extracted unit's own function will show as `excluded: not
extracted` in `candidates.txt` if `refresh-candidates.sh` is run before step 8, since the
candidate list is joined against whatever extraction is currently committed. That reading is
expected and correct, not a rejection; it resolves itself once step 8 runs.

## Step 7 — Spec-check and approve (core-only)

**Dev shell**: `default` (light).

```bash
bash scripts/spec-check.sh --core-only
bash approve.sh --review --spec <Module> --core-only --out FILE
# edit FILE
bash approve.sh --record FILE --approver "..." --core-only
```

## Step 8 — Extraction

**Where**: `framed_channel/aeneas/FramedChannelAeneas/Extracted/{Types,Funs}.lean` (regenerated),
`Extracted/FunsExternal.lean` (only if a new unmodeled external appears).

**Dev shell**: `.#extraction` (charon + aeneas on PATH).

```bash
nix develop .#extraction --command bash scripts/refresh-extraction.sh
```

This is a whole-crate `charon cargo --preset=aeneas` run — it re-extracts every unit, not just
the new one. Inspect the `Extracted/Funs.lean`/`Types.lean` diff. **If `FunsExternal.lean`
changes, model the new external name; never resolve it with an axiom.**

## Step 9 — Bridge

**Where**: `framed_channel/aeneas/FramedChannelAeneas/Bridge/<Unit>/*.lean`.

**Dev shell**: `.#extraction`, or `.#build`/`default` once `aeneas/`'s dependencies are already
fetched — building Lean against the extraction needs only the Lean toolchain plus the fetched
Aeneas/Mathlib, not charon/aeneas on PATH. `.#extraction` is simplest to stay in through step 13.

1. **Definitions.** `Bridge/<Unit>/Defs.lean` holds the abstraction function and every other
   definition a registered statement will mention. Import only extraction, specification and
   `Defs` modules; hold no proof unless it is a `shared-proof` row of `certificate/policy.txt`.
   **Every bridge module needs `open framed_channel`** (the namespace the extraction's own
   `Extracted/Funs.lean` wraps every generated declaration in — `crc8.crc8`, `varint.encode_u32`,
   etc.), alongside `open Aeneas Aeneas.Std Result`; every existing bridge file has it, but it is
   easy to miss since it is not one of the imports at the top of the file.
2. **Library gaps.** When `step*` stops at a library call, prove an `@[step]` specification of the
   library's own definition in `Bridge/Std.lean` — never an axiom.
3. **Loops.** Prove one loop lemma with `apply loop.spec_decr_nat (measure := ...) (inv := ...)`,
   then `unfold <fn>_loop.body; step*`, discharging goals branch by branch. Put the machine
   arithmetic in small `Nat` lemmas first.
4. **Refinement.** Every theorem is an Aeneas triple: total correctness, so error agreement and
   failure freedom as well as the success path.
5. **Interface instance — the canonical bridge pattern rule.** A simulation structure
   (`QueueSim`) is owed **only if the Rust dispatches through a trait AND a composite is proved
   generic over it** — today, only `BoundedQueue<T>`. Otherwise instantiate directly in
   `Instance.lean`, as `Varint` and `Crc8` do: define a tag, give it a `CodecModel`/`ChecksumModel`
   instance running the extracted functions through `Result.match`, and derive the laws from the
   refinement theorems. Do not build a `CodecSim`/`ChecksumSim` reflexively — ask the two-part
   question first.
6. **Code generic over a trait** (only when step 5 says a simulation is owed): state the bridge
   once over any record with a simulation, relate its state to the specification's structure at
   the extracted carrier, derive composites as corollaries, and instantiate at each concrete
   record last.

## Step 10 — Bridge registration

**Where**: `framed_channel/aeneas/FramedChannelAeneas/Registry.lean`.

**Dev shell**: as step 4a — `default` is enough for the script itself.

Same as step 4a, now with real bridge rows: read the current `bank.length` (bridge-only),
`allBank.length`, `totalScore allBank` and `totalMax allBank` values from the file's tail before
editing. Then:

```bash
bash scripts/refresh-hashes.sh --aeneas
```

Tag the model `[HAND-WRITTEN: model; bridged]` only once that run passes.

## Step 11 — Challenge module (bridge half)

**Where**: `framed_channel/aeneas/FramedChannelAeneasChallenge/<X>.lean` (new), plus the root
module.

**Dev shell**: `default` (light) once deps are fetched.

Restate each bridge theorem `:= sorry`, importing only extraction/`Defs` modules; add it to the
root module.

## Step 12 — Select/approve and spec-check/approve (bridge scope)

**Dev shell**: `.#extraction` for any script that touches charon; `approve.sh`/`spec-check.sh`
themselves are light once deps are fetched.

Repeat steps 6-7 with `--aeneas` in place of `--core-only`. `refresh-candidates.sh` need not
re-run if the Rust has not changed since step 6.

## Step 13 — Differential vectors

**Where**: `framed_channel/aeneas/GenVectors.lean`, `certificate/vectors.txt`,
`rust/tests/differential.rs`.

**Dev shell**: `default` (light) once `aeneas/`'s deps are fetched — the vector generator needs
only the Lean toolchain, not charon/aeneas on PATH.

Three concrete edits, all in `rust/tests/differential.rs` unless noted:

1. Add the unit's evaluation call to `aeneas/GenVectors.lean` if not already covered, then
   `bash scripts/refresh-vectors.sh` (runs `lake env lean --run GenVectors.lean`).
2. Add a `<unit>_agrees_with_extracted_vectors` test — mirror `queue_agrees_with_extracted_vectors`
   for a queue-shaped unit, or `crc8_agrees_with_extracted_vectors` for a stateless one.
3. Extend `extracted_vectors_cover_every_translated_operation`'s `branches`/`total` arrays with
   the unit's own `(op, status, detail)` rows — `branches` for multi-outcome operations, `total`
   for a single-outcome one (crc8's two operations are both `total`-only entries).

## Step 14 — Manifest

**Where**: `framed_channel/certificate/<snake_case_unit>.yaml`.

**Dev shell**: `default` (light).

Copy from the template:

```bash
cp framed_channel/certificate/templates/manifest.yaml framed_channel/certificate/<unit>.yaml
```

and fill it in, pointing at `certificate/shared.yaml` for the toolchain/recheck boilerplate. Add
`certificate/policy.txt` rows only if the unit introduces a shared-proof pair (a theorem whose
proof must live in a `Defs` module because another definition is built from it) or a flagged
compiler-trusting declaration.

## Step 15 — Gate

**Dev shell**: `.#extraction` (or let `full-gate.sh` auto-resolve it).

```bash
nix develop .#extraction --command bash check.sh
# or, from the repository root:
bash full-gate.sh --yes
```

Fix what it names and re-run to green. Then confirm nothing under `certificate/` changed beyond
what was expected, and commit the regenerated certificate
(`../../docs/development.md`'s "Certificate regeneration" section).

**Recheck staleness.** A new unit's `.rs`/`.lean` files are inside
`scripts/certificate-identity.sh`'s enumerated identity input set, so adding one changes the
certificate identity and leaves `certificate/recheck.txt` **stale**. Either re-run the
independent recheck (`bash check.sh --recheck` from `.#recheck` or `.#full`) or record the
staleness deliberately — do not leave it silently unaddressed. `.#recheck` on PATH is necessary
but **not sufficient**: `recheck/`'s own Lake targets (`lean4lean`, `lean4export`) must also be
built once, separately (`cd recheck && lake build lean4lean/lean4lean lean4export/lean4export`),
before `--recheck` can produce a complete record rather than a `certificate/recheck.partial.txt`
with `comparator`/`lean4lean` verdicts `NOT RUN`. That one-time build, not the recheck run itself,
is what actually takes time.
