# framed_channel

A worked example of the verification pipeline on one small piece of software: a framed message
channel in Rust, built from four components -- a `RingBuffer`, a list-backed queue (`VecQueue`),
a LEB128 `Varint` codec and a `Crc8` checksum -- plus the composite
`Channel`: five certified units. Each unit has a Lean model, an interface it instantiates, theorems,
registry rows and a certificate manifest; the composite is proved from the component theorems and
the interface laws alone. A Charon/Aeneas extraction of the whole crate is connected to all five
models by kernel-checked refinement theorems.

The gate requires the `aeneas/` package (the extraction and its bridge proofs), and with it the
Aeneas Lean library and therefore Mathlib: about 7 GB and a network fetch the first time, and
charon and aeneas on PATH. Two pre-checks end INCOMPLETE (exit 3), never PASS, and are not the
gate: `check.sh --core-only` is a fast offline development pre-check that leaves the bridge out
entirely, and `check.sh --committed-extraction` (only `jq` required) builds and audits both
packages against the committed extraction as-is, without invoking charon or aeneas.

## Running the checks

From this directory:

```
bash check.sh                        the verification gate (bridge included; see "What the gate checks")
bash check.sh --core-only            the fast offline pre-check, bridge left out (not the gate; see above)
bash check.sh --committed-extraction the light in-shell pre-check, bridge audited without charon/aeneas (not the gate; see above)
bash check.sh --recheck              also run the independent recheck (portable; Comparator is Linux only, see below)
bash check.sh --help                 every flag, the stage order and the prerequisites
```

From this directory, `bash ../full-gate.sh` resolves the fastest available route for your system
(prebuilt charon/aeneas where the pin has a release asset -- currently every supported system
except x86_64-darwin, see below) and
runs the gate; a plain `nix develop` alone supplies cargo, rustfmt, clippy, elan, jq, shellcheck,
actionlint, git and perl, but no charon/aeneas/comparator/landrun -- those come
only from `.#recheck`/`.#full` (see [../docs/development.md](../docs/development.md)):

```
bash ../full-gate.sh --yes
# or, when your system's pin has a prebuilt asset:
nix develop ..#extraction --command bash check.sh
```

On x86_64-darwin (no charon/aeneas route exists there at all), only `--core-only` or
`--committed-extraction` can run.

| Requirement | Needed for |
|---|---|
| bash >= 4.4, coreutils, awk, perl, elan (all supplied by the Nix dev shells; only the repository-root launchers `install.sh` and `full-gate.sh` run under the host bash, and they need only 3.2) | every run |
| cargo, rustfmt, clippy | every run except `--lean-only` |
| charon, aeneas, jq; network and about 7 GB on first fetch (Aeneas and Mathlib) | every gate run: an absent tool fails the gate (exit 2) before anything is built; `--core-only` leaves the bridge (and charon/aeneas/jq) out entirely; `--committed-extraction` needs only `jq`, never charon or aeneas |
| See `recheck/README.md` for the pinned tools and prerequisites | `--recheck` |

The dev shell provides the pinned `landrun` 0.1.17 on Linux, and, on x86_64-linux and
aarch64-linux, `comparator` too (both vendored under `../nix/`, see `flake.nix`). Under
`--core-only` or `--committed-extraction` a check whose tool is missing is skipped and reported as
such, never passed; under
the gate a missing tool is a failure. The two halves also
run directly: `cd lean && lake build`, and
`cd rust && cargo test` (which needs no Lean toolchain; it reads the committed vectors).

Other entry points, each with `--help`:

| Script | Purpose |
|---|---|
| `scripts/refresh-extraction.sh` | regenerate `aeneas/FramedChannelAeneas/Extracted/` after a Rust change |
| `scripts/refresh-vectors.sh` | regenerate `certificate/vectors.txt` by evaluating the extraction |
| `scripts/refresh-hashes.sh` | regenerate both registries' statement-hash columns |
| `scripts/refresh-candidates.sh` | regenerate `certificate/candidates.txt` from the Charon LLBC |
| `scripts/spec-check.sh` | print SpecCheck's records over the Challenge libraries |
| `approve.sh` | `--review` writes a review file of the stale approvals; `--record` records the reviewed ones (a person at a terminal, or an agent with `--agent`) |
| `scripts/check-approvals.sh` | verify the approvals alone (read-only) |
| `scripts/certificate-identity.sh --check` | does the committed certificate name this tree? (no build) |
| `scripts/certificate-freshness.sh` | did the just-run gate leave `certificate/` exactly as committed? (used by `verify.yml`'s "Certificate freshness" step, after the gate) |
| `scripts/comparator-configs.sh` | derive the Comparator configs into a temporary directory |
| `scripts/adopt-recheck.sh` | adopt a CI-produced, complete `recheck.txt` (not a certificate-identity input) |
| `tests/` | nine fixture-test runners covering the gate's own tools (approvals, proof ladder, license headers and more); see `tests/README.md` for the full list |

**Select, Specify and approve.** Which Rust items the claims are about, and which Lean statements
say what each unit should do, are judgements recorded with `approve.sh`, by a person or an agent:

From this directory:

```bash
bash approve.sh --review --aeneas --out /tmp/review.md   # absent or stale items
# review /tmp/review.md: write findings under Notes, mark approved items "yes"; then either
bash approve.sh --record /tmp/review.md --approver "Name <email>" --aeneas
bash approve.sh --record /tmp/review.md --approver "Name (agent) <email>" --agent --aeneas
```

The selection is made from `certificate/candidates.txt` and bound to a sha256 of the Rust sources;
each approved specification is a statement-only Challenge module bound to a digest of everything
its statements depend on. `check.sh` never writes approvals, and its final stage fails until they
are recorded and current. Details and limits: `certificate/README.md`, "Select, Specify and
approval".

**Independent recheck.** `check.sh --recheck` (several minutes) rechecks the proofs with checkers
other than the build. It is always over both packages (`--core-only --recheck` is refused). The
kernel replay (Lean4Lean, leanchecker) runs on any platform;
Comparator needs Linux's Landlock sandbox and is `NOT-RUN`
elsewhere. A run whose record is complete (no verdict `NOT-RUN` outside `lean4lean-fresh`'s --
that line is always emitted, but only runs, rather than reporting `NOT-RUN`, with
`--recheck-fresh`) writes `certificate/recheck.txt`; any other run -- e.g.
Comparator on macOS -- writes the same content instead to the gitignored
`certificate/recheck.partial.txt`, never `recheck.txt`. A later plain run reports one of four
outcomes: `recheck.txt` current and a pass, current but recording a `FAIL` verdict, current but
PARTIAL, or STALE -- never a pass for anything but a current, complete record. CI produces
a complete record on hosted Linux and uploads it; `scripts/adopt-recheck.sh` adopts it locally
for a contributor without a Linux host. What each checker establishes is in `certificate/README.md`
("recheck.txt"); `recheck/README.md` covers the pinned tools and the full platform detail.

## What the gate checks

In order: revision coherence and extraction staleness; the layer import rule; license headers;
each package's build, with a scan for `sorry`, `native_decide`, search tactics and vacuous
definitions; registry statement hashes; specification and selection consistency; differential
vectors; the axiom audit; the proof ladder; the manifest cross-check; the independent recheck
record; `cargo fmt --check`, `cargo clippy` and `cargo test`; that the certificate identity did not
change during the run; and last, the approvals. A run red only at the approvals stage means
"not yet (re-)approved". The full list of failure conditions is in `certificate/README.md`, "What
the gate enforces".

The gate regenerates `certificate/axioms.txt`, `digests.txt`, `ladder.txt` and `countermodels.txt`
on every full run; never edit them. A `--core-only` or `--committed-extraction` run writes nothing
under `certificate/` (its
outputs go to the run's temporary directory), so a pre-check can never leave a weakened
certificate behind. They name the certificate identity (a sha256 of the gate's inputs), not a
timestamp or commit, so an unchanged tree regenerates them byte for byte and
`scripts/certificate-identity.sh --check` catches a certificate not regenerated for its tree, or one
whose `axioms.txt` did not audit every package.

## Proof ladder

The Prove step's rule is "cheapest method first: simp, grind, retrieval, AI provers,
countermodels". Here simp, grind, retrieval, manual and countermodels are enforced by the build;
AI provers are not demonstrated.

**The rungs**, cheapest first: `decide < simp < omega < grind < retrieval < bv_decide < manual`.
Every registered core theorem is proved as `:= by rung <method> => <script>`
(`lean/FramedChannel/Ladder.lean`). Where the theorem is declared, the tactic

1. checks the script is in the method's syntax class (`simp` is one simp call naming no theorem;
   `retrieval` names a library theorem; `manual` is anything);
2. tries every strictly cheaper rung on the same goal, with one canonical tactic each and a fixed
   heartbeat budget, and fails the build naming the first that closes it (a closer that relies on
   `sorry` does not count);
3. runs the script as the proof and logs `ladder <declaration> <method>`, which the gate collects
   into `certificate/ladder.txt`.

**What `manual` means.** A script a person or an outside tool wrote; the gate cannot tell which and
does not claim to. There is no AI-prover rung and no extension point for one.
`crc8_step_linear_kernel` is recorded `manual (excluding bv_decide)`: its audit skips the
`bv_decide` rung it exists to avoid.

**Records not audited as rungs.** The shared-proof pair `RingBuffer.push_inv`/`pop_inv` lives in
the approved definitions layer, so wrapping it would move the approved digests; `ladder_record%`
records it after the fact, with the retrieval audit not run. The four class instances are recorded
as `instance`, with no audit claimed.

**Countermodels.** `lean/FramedChannel/Evidence/Countermodels.lean` refutes rejected candidate
statements in the kernel: the varint theorems without `n < 2 ^ 32`, a receiver that treats a
second `0x7E` as a new boundary, and `idx_ne` with `i ≤ len`. Each witness is the first failure of
a `decide +kernel` search over an explicit enumeration, recorded by `refuted%` into
`certificate/countermodels.txt`. The search covers only the domain it is given. Nothing imports
the module, and its theorems are evidence, not registered obligations.

**Limits.** The verdicts belong to the pinned toolchain: a newer `simp` or `grind` may close a goal
recorded above it, and the build then fails naming the cheaper rung. The bridge rows (Aeneas `step`
scripts) are not laddered and are reported NOT CHECKED.

## Architecture

The Lean code is organized extraction-first: the Rust is extracted mechanically, and everything
hand-written either specifies what the extraction must satisfy or proves that it does.

```
┌───────────────────────────────────────────────────────────────────────────────┐
│ Registries and certificates                                                   │
│   lean/FramedChannel/Registry.lean, aeneas/FramedChannelAeneas/Registry.lean, │
│   certificate/*.yaml (proofs: = registered names), axioms.txt, digests.txt,   │
│   candidates.txt, policy.txt, approvals.yaml (approve.sh; by person or agent) │
└───────────────────────────────────────┬───────────────────────────────────────┘
                                        │ bind by statement hash and approval digest
┌───────────────────────────────────────┴───────────────────────────────────────┐
│ Challenge  lean/FramedChannelChallenge/, aeneas/FramedChannelAeneasChallenge/ │
│   the approved statements, restated with := sorry (not a default target)      │
└───────────────────────────────────────┬───────────────────────────────────────┘
                                        │ same names and statement hashes
┌───────────────────────────────────────┴───────────────────────────────────────┐
│ Composition  lean/FramedChannel/Composition/                                  │
│   Channel theorems proved from the queue laws alone                           │
├───────────────────────────────────────────────────────────────────────────────┤
│ Bridge       aeneas/FramedChannelAeneas/Bridge/   (hand-written)              │
│   QueueSim, transport theorems and the extracted-carrier instance; per        │
│   component a Defs module, refinements and interface instances                │
├───────────────────────────────────────────────────────────────────────────────┤
│ Model        lean/FramedChannel/Model/            (hand-written)              │
│   reference models: abstraction targets, evaluable semantics, law instances   │
├───────────────────────────────────────────────────────────────────────────────┤
│ Specification  lean/FramedChannel/Spec/                                       │
│   Result; L0 interfaces QueueModel, CodecModel, ChecksumModel; L1 laws        │
├───────────────────────────────────────────────────────────────────────────────┤
│ Extracted    aeneas/FramedChannelAeneas/Extracted/  (generated, never edited) │
│   charon/aeneas output for the whole rust/ crate                              │
└───────────────────────────────────────────────────────────────────────────────┘
```

Every layer from Model up is split in two: `Defs` modules hold the definitions a statement
mentions, and the rest hold the theorems. The Challenge libraries import only specification,
`Defs`, extraction and Aeneas modules, so the approved statements and the proofs share one set of
definitions. The one pair of proofs inside `Defs` is `RingBuffer.push_inv`/`pop_inv` (the
`shared-proof` rows of `certificate/policy.txt`).

The two packages split at the dependency that costs 7 GB: `lean/` (Specification, Model,
Composition, the core registry) builds against core Lean alone, and `aeneas/` (Extracted, Bridge,
the bridge registry) requires Aeneas and Mathlib. The laws are stated once, over the specification's
own `Result`; an extracted carrier reaches them through its interface's simulation structure
(`QueueSim`), not a restated copy. `check.sh` enforces the layer edges by import.

## Directory layout

| Path | Contents |
|---|---|
| `check.sh` | the verification gate |
| `approve.sh` | the approval tool |
| `scripts/lib/packages.sh`, `scripts/lib/aeneas-revs.sh`, `scripts/lib/approval-digests.sh`, `scripts/lib/recheck-revs.sh` | helpers sourced by the scripts: the package tables and Lean-source parsers, the Aeneas revision check, the approval digests, the recheck tool probes |
| `scripts/refresh-*.sh` | the writers of the generated extraction, vectors, hashes and candidates |
| `scripts/spec-check.sh`, `scripts/check-approvals.sh` | Specify records, the approval tool's read-only checker |
| `scripts/certificate-identity.sh`, `scripts/certificate-freshness.sh`, `scripts/check-spdx.sh` | the certificate identity; whether a fresh gate run would change the committed certificate; the license-header check |
| `scripts/comparator-configs.sh`, `scripts/recheck-comparator.sh`, `scripts/recheck-kernel.sh`, `scripts/recheck-record.sh`, `scripts/adopt-recheck.sh` | the independent recheck; rendering the verdicts and writing `recheck.txt`/`recheck.partial.txt`; adopting a CI-produced, complete `recheck.txt` |
| `rust/` | the crate ([README](rust/README.md)) |
| `lean/` | specifications, models, composition, core registry, core Challenge library ([README](lean/README.md)) |
| `aeneas/` | the extraction, bridge proofs, bridge registry and Challenge library, vector generator ([README](aeneas/README.md)) |
| `recheck/` | the pinned Lean4Lean and lean4export builds and the landrun shim ([README](recheck/README.md)) |
| `certificate/` | manifests, policy, approvals and generated audit files ([README](certificate/README.md)) |
| `tests/` | nine fixture-test runners covering the gate's own tools; see `tests/README.md` |
| `docs/adding-a-unit.md` | the end-to-end procedure for adding a protocol-scoped unit to this worked example |

The repository root's `flake.nix` pins the dev shell: Rust 1.95.0, elan, jq, perl and git
always; charon and aeneas (both, on every currently-supported system -- see
`../nix/aeneas-pin.json` for the exact pinned release tag and revision) only where `.#extraction`,
`.#recheck` or `.#full` is entered, never the light `.#default`. On x86_64-linux and
aarch64-linux, `.#recheck`/`.#full` also pin comparator (see `../docs/development.md`'s "Pinned
versions" table for its current revision, vendored under `../nix/comparator.nix`) and the
prebuilt Lean toolchain that builds it, plus the vendored landrun 0.1.17. Lean itself, for the two
Lake packages above, is installed by elan and its dependencies by Lake.

## The six-step map

Verifying existing Rust takes six steps; this is where each one is. Not demonstrated: `hax` (the
extraction is Charon/Aeneas only), synthesizing new Rust, and AI provers.

| Step | File, declaration or command |
|---|---|
| 1. Select | `certificate/candidates.txt` (`scripts/refresh-candidates.sh`); `approve.sh --review --selection --aeneas`, then `--record ... --aeneas`, records the decision; `scripts/check-approvals.sh` verifies it |
| 2. Model | `scripts/refresh-extraction.sh` regenerates `aeneas/FramedChannelAeneas/Extracted/`; `aeneas/FramedChannelAeneas/Bridge/` connects it to the hand-written models; `rust/tests/differential.rs` checks the Rust against vectors computed by evaluating the extraction |
| 3. Specify | the Challenge modules `lean/FramedChannelChallenge/` and `aeneas/FramedChannelAeneasChallenge/`; `scripts/spec-check.sh --aeneas` prints their records; `approve.sh --review --spec MODULE --aeneas`, then `--record ... --aeneas`, records the approval |
| 4. Elaborate | `register%` (`lean/FramedChannel/Certify.lean`) binds a theorem to its registry row and statement hash, one theorem per claim |
| 5. Prove | the proof ladder (`lean/FramedChannel/Ladder.lean`), `certificate/ladder.txt`, `certificate/countermodels.txt` |
| 6. Certify | `check.sh`, `check.sh --recheck`, `certificate/recheck.txt` |

## The relations, and where each one is

Relations about executed code have a Rust and a Lean counterpart; distillation and decidability
are Lean-only.

| Relation | Rust | Lean |
|---|---|---|
| Refinement (`A ⊑ C`) | the `BoundedQueue<T>` trait, exercised by `check_bounded_queue_laws` | `instBoundedQueueLaws` on `RingBuffer.BQ` and on `VQ`, `Varint.instCodecLaws`, `Crc8.instChecksumLawsBitwise`; on the extracted code, `instBoundedQueueLaws_extracted` (ring buffer and `VecQueue`), `instCodecLaws_extracted`, the two extracted `ChecksumLaws` instances |
| Equivalence (`A ≃ B`) | `crc8_bitwise_agrees_with_table` | `crc8_table_eq_bits`, and `instChecksumLawsBitwise`/`instChecksumLawsTabled`: one interface, two models; on the extracted code, `crc8_table_eq_extracted` |
| Composition (`B ∘ A`) | `Channel::send` and `Channel::deliver` | `encodeFrame`/`send`/`deliver` and `send_deliver`; on the extracted code, `send_deliver_extracted` over any lawful queue record |
| Round trip (`D ∘ E = id`) | `varint_roundtrip_on_fixed_inputs` | `varint_roundtrip`; on the extracted code, `roundtrip_extracted` (no bound hypothesis) |
| Substitution (`C[B/A]`) | `Channel<Q = RingBuffer<Frame>>`, run at `VecQueue<Frame>` too | `deliver_spec_RB`/`deliver_spec_VQ`: one proof, two queues; on the extracted code, `send_deliver_extracted_RB`/`_VQ` and `send_deliver_from_new_RB`/`_VQ` |
| Inheritance | every `_vec_queue` test is the same body at a second instance | every channel theorem is proved from the six laws; none opens `RingBuffer` or `VQ` |
| Distillation | -- | the `inv_preserve` and `refine_commute` tactics, with the measured reuse table in `Model/RingBuffer/Theorems.lean` |
| Decidability | -- | `bv_decide` (bit-vectors bit-blasted to SAT), the 256-case kernel `decide`, the ladder's `decide` rung, and the kernel countermodel searches |

## Unit names

**The canonical name of a unit is its Rust type name.** Every other spelling of that unit is
derived from it by a fixed convention, so there is one name per unit and the sixth component can
be named without inventing anything.

| Rust | extraction module | model namespace / type | Challenge modules | bridge namespace | instantiation suffix | manifest |
|---|---|---|---|---|---|---|
| `RingBuffer<T>` (`src/ring_buffer.rs`) | `ring_buffer` | `FramedChannel.RingBuffer` / `BQ` | `FramedChannelChallenge.RingBuffer`, `FramedChannelAeneasChallenge.RingBuffer` | `FramedChannel.Bridge.ring_buffer` | `_RB` | `certificate/ring_buffer.yaml` |
| `VecQueue<T>` (`src/queue.rs`) | **`queue`** (the one exception, below) | `FramedChannel.VecQueue` / `VQ` | `FramedChannelChallenge.VecQueue`, `FramedChannelAeneasChallenge.VecQueue` | `FramedChannel.Bridge.vec_queue` | `_VQ` | `certificate/vec_queue.yaml` |
| `Varint` (`src/varint.rs`, free functions) | `varint` | `FramedChannel.Varint` / `Leb128` | `FramedChannelChallenge.Varint`, `FramedChannelAeneasChallenge.Varint` | `FramedChannel.Bridge.varint` | -- (one model) | `certificate/varint.yaml` |
| `Crc8` (`src/crc8.rs`, free functions) | `crc8` | `FramedChannel.Crc8` / `Bitwise`, `Tabled` | `FramedChannelChallenge.Crc8`, `FramedChannelAeneasChallenge.Crc8` | `FramedChannel.Bridge.crc8` | `Bitwise` / `Tabled` | `certificate/crc8.yaml` |
| `Channel<Q>` (`src/channel.rs`) | `channel` | `FramedChannel.Channel` / `Chan` | `FramedChannelChallenge.Channel`, `FramedChannelAeneasChallenge.Channel` | `FramedChannel.Bridge.channel` | `_RB` / `_VQ` | `certificate/channel.yaml` |

The conventions the table encodes:

- the **model namespace** is `FramedChannel.<RustType>`, and the **bridge namespace** is its
  `snake_case`;
- the **Challenge module** is `<RustType>` in each package's Challenge library;
- the **manifest** is `snake_case(<RustType>).yaml`, named for the unit and not for one of its
  operations -- a manifest covers the whole unit;
- an **instantiation suffix** is the unit's two-letter abbreviation (`_RB`, `_VQ`), used where one
  generic theorem is instantiated at several units.

**The one justified exception: the extraction module of `VecQueue<T>` is `queue`, not
`vec_queue`.** The extraction module name is chosen by Charon from the Rust *file* name, and
`src/queue.rs` holds the `BoundedQueue` trait alongside the `VecQueue` type, so the file is named
for the interface rather than for the type. Splitting the file would remove the exception but
would restale the recorded *selection* approval (`source_sha256` hashes every `src/*.rs` byte) and
force a full `scripts/refresh-extraction.sh` run, so the exception stays and is recorded here
instead.

**The forward rule for the next component: one Rust file per unit, named for the unit's type, and
a trait gets its own file.** Follow that and the extraction module name comes out canonical with
no exception to document.

One residual, recorded rather than hidden: the ring buffer's model type is `BQ`, for *bounded
queue* -- the interface it implements -- while the second queue's is `VQ`, for its unit. The unit
NAMES are canonical (the table above), and `BQ` is only a two-letter type abbreviation inside
`FramedChannel.RingBuffer`, but a future task that is already restaling the ring buffer's hashes
for another reason should rename it `RB` and remove the last spelling that is not derived from its
unit.

## The component anatomy

Every unit has the same anatomy. The `coverage:` block of each manifest states, obligation by
obligation, which are proved and which are not claimed.

| Obligation | Where |
|---|---|
| L0 operational interface (operations and types, no laws) | `QueueModel`, `CodecModel`, `ChecksumModel` |
| L1 laws class (a `Prop` class over an abstract observation) | `BoundedQueueLaws` (over `toList`), `CodecLaws` (over decoding), `ChecksumLaws` (over the digest) |
| canonical model, so the interface is not vacuous | `RingBuffer.BQ`, `VecQueue.VQ`, `Leb128`, `Bitwise` and `Tabled` |
| representation invariant | `RingBuffer.Inv`; the others need none, and say so |
| abstraction function and refinement | `contents`, with `push_contents`/`pop_contents` |
| error agreement | `push_ok`/`push_fail`, `pop_ok`/`pop_fail`; extracted: `push_full`/`pop_empty`, `decode_err_iff`, `send_refines`/`deliver_refines`; and the error records in `certificate/vectors.txt` |
| bounds or failure freedom | `RingBuffer.push_bounded`, `VecQueue.push_bounded`, `encode_length_le`, `stepTable_index_in_range`, `send_bounded` |
| registry row bound to the statement hash | both `Registry.lean` files, through `Certify.lean`'s `register%` |
| certificate with provenance and trust | `certificate/*.yaml` |
| differential test | `rust/tests/differential.rs` against `certificate/vectors.txt` |

The per-component Rust-to-Lean mapping tables are in the module docstrings.

## Scope and standing limits

- **The models are hand-written; the extraction is trusted.** Each model is connected to the real
  Charon/Aeneas extraction by kernel-checked refinement theorems, and the specification's laws are
  instantiated directly on the extracted carriers. The ring buffer's instance assumes `Clone` is
  the identity, proved for the `Vec<u8>` frames actually queued. The channel theorems keep two
  genuine hypotheses (room on the wire; `len + in_flight <= usize::MAX`, which the channel invariant
  discharges) and state the parser's wide-length divergence as a case split. The extractor itself
  (rustc MIR, Charon, Aeneas and its library models) is trusted, not verified; five library
  functions Aeneas does not model are supplied as crate-local definitions with proved specs.
- **`verified` is never applied to a whole unit**; see `certificate/README.md`, "Trust verdicts".
- **The differential suite is finite testing on fixed vectors**, not a proof: `validated`
  evidence about the translation on the recorded inputs only. The staleness chain is `rust/src` to
  the extraction, the extraction to `certificate/vectors.txt` (bridge package only), and the vectors
  to the Rust (`cargo test`).
- **The frame-corruption and resynchronization scenario has no concrete referent here.** It
  illustrates Logos properties, but is not implemented.
- **Approval rests on process.** The gate checks that each approval is current, not who made it.
- Corruption on the wire, concurrency and the compiled binary are outside every certificate.

The fixed tag vocabulary is in `certificate/README.md`.

## Navigation

- [rust/](rust/README.md) - the crate
- [lean/](lean/README.md) - the specifications, models and proofs, layer by layer
- [aeneas/](aeneas/README.md) - the extraction and the bridge proofs
- [recheck/](recheck/README.md) - the pinned independent-recheck tools
- [certificate/](certificate/README.md) - the receipts, generated audit files and the gate's rules
- [docs/adding-a-unit.md](docs/adding-a-unit.md) - the end-to-end add-a-unit procedure
- [Parent Directory](../README.md)
