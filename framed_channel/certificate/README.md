# certificate/

The machine-readable receipts of the worked example: what was checked, under which axioms, what a
person approved, and what is explicitly not claimed. This README is also the canonical statement
of what the gate (`../check.sh`) enforces; `bash ../check.sh --help` is the canonical flag list.
See [../../docs/trust-model.md](../../docs/trust-model.md) for the summary of what a green badge
or a valid certificate does and does not certify.

| Kind | Files | Written by |
|---|---|---|
| Manifests | `ring_buffer.yaml`, `vec_queue.yaml`, `varint.yaml`, `zigzag.yaml`, `crc8.yaml`, `stuff.yaml`, `channel.yaml` | hand |
| Shared manifest content | `shared.yaml` | hand |
| Policy | `policy.txt` | hand |
| Approvals | `approvals.yaml` | a person or a declared agent, through `../approve.sh` only |
| Generated on every gate run | `axioms.txt`, `digests.txt`, `ladder.txt`, `countermodels.txt` | `../check.sh` |
| Generated on a recheck run | `recheck.txt` | `../check.sh --recheck` |
| Generated on request | `vectors.txt` | `../scripts/refresh-vectors.sh` |
| Generated on request | `candidates.txt` | `../scripts/refresh-candidates.sh` |

Generated files are never edited by hand.

## Manifests

There is one manifest per certified unit: the six components (ring buffer, list-backed queue,
varint codec, zigzag signed-varint codec, CRC-8, byte stuffing) plus the composite channel. All
seven share one shape: `component`, `source`,
`formal_model`, `bridge`, `implements` (or `composition` for the composite), `assumptions`,
`guarantees`, `proofs`, `supporting`, `dependencies`, `toolchain`, `coverage`, `trust`,
`not_claimed`, plus a `specification:` block naming the Challenge modules its `proofs:` are
checked against and a `selection:` block pointing at the selection record in `approvals.yaml`.

Adding a new manifest starts from `templates/manifest.yaml`: the fixed skeleton above, sized
against what `shared.yaml` already factors out, with a header comment naming which existing
manifest to read for each unit-specific-key block a new unit might not need. Copy it, never
generate it; `../check.sh`'s manifest glob ignores the template itself (see
`## Hand-written files` below).

`toolchain:` and `trust.G0_checker.independent_recheck:` each carry `shared: certificate/shared.yaml`.
`shared.yaml` holds the content every manifest shares: the common toolchain pointers (Lean, the
extractor, the Rust toolchain, the certificate identity, and, for the five units that share it,
`mathlib`/`build`) and the independent-recheck entries (comparator, lean4lean, leanchecker,
nanoda). Each manifest keeps only its own delta: `toolchain.extraction:` (the unit-specific tail
of what was extracted), and, where a unit's `mathlib`/`build` differs from the shared value (today
only `ring_buffer.yaml`), its own override. A manifest never restates a toolchain revision;
it points at the pin file (`../nix/aeneas-pin.json`, `../flake.lock`, `aeneas/lake-manifest.json`,
`lean/lean-toolchain`, `rust-toolchain.toml`) or the generated record
(`certificate/candidates.txt`, `certificate/recheck.txt`) instead, and `../check.sh`'s manifest
cross-check stage enforces this mechanically, both structurally (every manifest must point at
`shared.yaml` and must not restate its entries) and with a revision-token lint that fails on any
hex revision or version triple in a manifest or in `shared.yaml`.

Some units extend the shared shape with unit-specific keys: `purpose` and `recorded_difference`
(`vec_queue.yaml`), `findings` (`varint.yaml`, `channel.yaml`), `composite_trust_note`
(`crc8.yaml`, `channel.yaml`), and `trust.G0_checker.independent_recheck.flagged_rows`
(`crc8.yaml`, its two `crc8_step_linear` notes that do not belong in the shared file).

`proofs:` lists the **certified obligations**: every name is a registered, statement-hash-bound
row of `../lean/FramedChannel/Registry.lean` (core package) or
`../aeneas/FramedChannelAeneas/Registry.lean` (bridge package). `supporting:` lists the lemmas
those obligations are built from: proved and audited, but not registered.

| File | What to read it for |
|---|---|
| `ring_buffer.yaml` | the fully worked component: model proofs, the extracted-code bridge by name, and the `trust` block with all six ground classes |
| `vec_queue.yaml` | its `purpose` block (without a second queue, substitution has nothing to substitute) and its `bridge` block |
| `varint.yaml` | its `coverage` block (how a stateless component handles state-shaped obligations) and the extracted round trip whose `u32` bound is carried by the machine integer |
| `crc8.yaml` | the one compiler-trusting declaration and the one-entry allow-list that permits it |
| `stuff.yaml` | its `countermodels` block, where the search enumeration is sized to stay decidable in the kernel |
| `zigzag.yaml` | the unit defined OVER another: both model laws and two of the four bridge theorems are retrieved from the varint's, which its `ladder` and `findings` blocks record, and its `countermodels` block distinguishes the two boundaries its three refutations pin |
| `channel.yaml` | its `composition` block (`send = push ∘ checksum ∘ encode`) and its `findings` block (the length-126 case) |

`crc8.yaml` and `channel.yaml` each carry a `composite_trust_note` naming their weakest link.

### Ground classes G0-G5

Each manifest's `trust` block gives one verdict per ground class, the places a certificate can be
wrong:

| Class | Question |
|---|---|
| `G0_checker` | Is the proof checker sound, and do the proofs use only the trusted axioms? |
| `G1_translation` | Does the Charon/Aeneas translation of the Rust mean what the Rust means? |
| `G2_ir_faithfulness` | Do rustc MIR and Charon's LLBC faithfully represent the Rust? |
| `G3_models` | Are the library models (Aeneas's `Vec`, scalars, the crate-local externals) right? |
| `G4_specification` | Do the approved statements say what the component should do? |
| `G5_binding` | Is the certificate bound to exactly these sources and statements? |

### Trust verdicts

Exactly three, used verbatim:

| Verdict | Meaning |
|---|---|
| `verified` | a machine decided it, and the decision is reproducible here |
| `validated` | evidence supports it, short of a proof (differential execution) |
| `trusted` | accepted without either, and the reason is stated |

**`verified` is never applied to a whole component.** The only component-level `verified` verdict
is `G5_binding`. The other `verified` verdicts are the scoped
`trust.G0_checker.independent_recheck` entries for Comparator and Lean4Lean, each bounded by its
`establishes:` and `not_established:` lines and holding only while `recheck.txt` is current. The
top-level `G0_checker` verdict stays `trusted`. `G4_specification`'s `approval_verdict` is
`trusted`: that a statement says the right thing is a human judgment. A composite is never more
trusted than its least trusted part.

### Tag vocabulary

Fixed, and used verbatim in module docstrings and manifests. Challenge modules and Rust files
carry no tag.

| Tag | Meaning |
|---|---|
| `[PROVED: kernel]` | sorry-free; `#print axioms` within `{propext, Classical.choice, Quot.sound}` |
| `[PROVED: compiler-trusting]` | sorry-free but uses `bv_decide` (a native helper axiom is present). Exactly one declaration: `FramedChannel.Crc8.crc8_step_linear` |
| `[HAND-WRITTEN: model; bridged]` | a hand-written Lean model (`../lean/FramedChannel/Model/`, `Composition/`) in the shape Aeneas produces, connected to the extraction by the bridge proofs in `../aeneas/` |
| `[HAND-WRITTEN]` | hand-written bridge infrastructure in `../aeneas/FramedChannelAeneas/Bridge/` that is not a model: library step specifications (`Std.lean`), the trait-record assumptions (`Queue/Traits.lean`), the generic queue simulation and its instance (`Queue/Defs.lean`, `Queue/Transport.lean`, `Queue/Instance.lean`), and the per-component abstraction and definitions modules (`<X>/Defs.lean`, `Channel/Abstraction.lean`) |
| `[EXTRACTED: aeneas + bridge]` | connected to a Charon/Aeneas extraction of the Rust by kernel-checked refinement theorems (`../aeneas/FramedChannelAeneas/Bridge/`). The extractor (rustc MIR, Charon and Aeneas, Aeneas's library models and the crate-local models in `Extracted/FunsExternal.lean`) is trusted, not verified; the tag carries no revision so a pin bump never touches it -- the pinned revisions live in `../../nix/aeneas-pin.json` and `../flake.lock`, with the charon version that produced the committed extraction recorded in `candidates.txt`; no manifest restates them. All seven units carry it |
| `[AUTHORED: nix-tested]` | Rust written here (manifests only); toolchain from PATH, or pinned by the root `rust-toolchain.toml` (read by `flake.nix`) when used; `../check.sh` runs `cargo fmt --check`, `cargo clippy -D warnings` and the differential tests, locally and in CI (`.github/workflows/ci.yml`, `verify.yml`) |
| `[NOT CLAIMED]` | explicitly outside the certificate (the compiled binary, concurrency, corruption on the wire) |

## Select, Specify and approval

The Select and Specify steps end in judgements. Here they are recorded, checkable artifacts
that also say who made each one: a person or an agent.

**Select.** `candidates.txt` is generated from one whole-crate `charon cargo --preset=aeneas` run:
one tab-separated row per local item (function, trait-impl method, const) with its extracted Lean
name, Rust path, source span, visibility, kind, whether it is a derived impl, and a verdict,
`in-subset` or `excluded` with every failed criterion named. The criteria are syntactic checks:
two are per-item, read from unshared LLBC fields only (the crate forbids `unsafe_code`; the item
is not `unsafe` and writes no raw pointer or `static mut`); one is crate-wide and regex-based
(`../scripts/refresh-candidates.sh`'s `DENY_RE`, matched against every translated declaration's
path, local or library -- an empty match is applied identically to every item, since the LLBC's
hash-consing does not let a per-item reachability walk be resolved soundly from the JSON alone);
Aeneas translates it. Standard-library internals are not audited (G3). A
reviewer then marks each in-subset item *selected* or *declined* (with a reason). The record is bound
to `source_sha256` (over `../rust/src/*.rs`, `Cargo.toml` and `Cargo.lock`) and
`candidates_sha256`, both defined in `../scripts/lib/approval-digests.sh`. `Cargo.toml` and
`Cargo.lock` are digested through a version-normalized view: the root package's own `version`
field (in `Cargo.toml`'s `[package]` table and in the lockfile's own `[[package]]` block) is
excluded, since it affects no compiled behavior and no proof -- everything else (dependency
versions, the lockfile format version, `edition`, `rust-version`, features, targets) is still
hashed verbatim.

**Specify.** The approved specification is Lean text: one statement-only Challenge library per
package (`../lean/FramedChannelChallenge/`, `../aeneas/FramedChannelAeneasChallenge/`), one module
per component (plus the bridge's `Queue` module for the generic transport theorems and the `Clone`
assumption), restating every registered theorem with `:= sorry`, the form Comparator consumes. The
definitions the statements mention live in `Defs` modules that both the Challenge and the proofs
import. The Challenge is maintained by hand and never regenerated from the proofs. Each module's
record carries its `spec_digest`, computed by `../lean/FramedChannel/SpecCheck.lean`: a fold over
the module's statement hashes and every constant in their transitive closure (definition bodies,
extracted functions, library definitions, embedded proof terms), walked as Comparator walks it.

**The approval unit** is the Challenge module: not a single theorem (that would duplicate the
registry) and not a manifest (a manifest may rely on another component's module, and the bridge
half must be checkable on its own).

**Re-approval is required** when a statement changes; when a definition, extracted function or
library definition in a statement's closure changes (so any Rust change that alters the
extraction, and any Lean, Aeneas or Mathlib bump); when a proof term embedded in that closure
changes (the shared-proof pair); and, for the selection, when any file under `../rust/src`, a Cargo
file or the candidate set changes, a comment included -- **except** the root package's own
`version` field in `Cargo.toml`/`Cargo.lock`, which `source_sha256` excludes (see Select, above).
Lean comments, docstrings and source positions do not change a digest.

**Digest scope.** `spec_digest` is a 64-bit structural hash fold: a change detector bound to this
toolchain, not a cryptographic commitment. The two sha256 digests are file-level. Comparator's run
over the Challenge and the registry (see "recheck.txt") is the exact statement check.

**How approval works.** `../approve.sh` is the only writer of `approvals.yaml`, in two steps.
`--review` (no terminal needed) writes one review file: a Decisions block with every item set to
`no`, a pre-filled selected/declined draft, and the evidence (digests, the diff since the last
approval, the candidate table, each Challenge module's text). By default it covers every absent
or stale item. A reviewer reads it, edits the draft, marks items `yes` and writes their findings
under Notes. `--record FILE --approver "..."` then re-computes every digest, refuses if a marked
item changed since the review, and writes only the marked records, each with `by:`:

| Recorded by | Command | Requires | Record |
|---|---|---|---|
| a person | `--record FILE --approver "Name <email>"` | a terminal and one typed confirmation | `by: person` |
| an agent | `--record FILE --approver "Name (agent) <email>" --agent` | findings under Notes; no terminal | `by: agent` |

An agent's approver name must end in `(agent)` and a person's must not; `../scripts/check-approvals.sh`
enforces that pairing. The Notes are not copied into `approvals.yaml`; keep the review file if the
reasoning should be kept. `approve.sh` never commits, and `../check.sh` never writes the file; its
final stage fails while any record is absent or stale. By default the gate accepts records of
either kind; `check.sh --require-person-approval` fails any `by: agent` record, for a release that
must rest on a person's judgement.

**Limitation.** `by:` is declared, not detected: the tool cannot tell a person from a program that
has a terminal, and agents and people commit under the same git identity in this repository. A
`by: person` record therefore rests on the process rule that an agent always records with
`--agent`, not on anything the gate checks.
What the gate does decide is that each record is about exactly the Rust, candidates, statements and
definitions in the tree now.

## Hand-written files

### templates/manifest.yaml
The copy-from skeleton for a new manifest (see `## Manifests` above for the pointer and
`../docs/adding-a-unit.md`'s manifest step). One directory below `certificate/`, so
`../check.sh`'s manifest list (`printf '%s\n' "$CERT"/*.yaml`, non-recursive) never treats it as a
real manifest and never validates its placeholder values.

### policy.txt
Read by `../check.sh` and `../scripts/comparator-configs.sh`: the `trusted` axioms (the audit's trusted set
and Comparator's `permitted_axioms`), the `flagged` allow-list, and the `shared-proof` rows. A
shared-proof row is a registered theorem whose proof lives in the definitions layer because a
definition is built from it: `RingBuffer.push_inv` and `pop_inv`, from which `pushBQ` and `popBQ`
build the invariant subtype. The Challenge imports those two proved instead of restating them.

### approvals.yaml
Shape:

```yaml
selection:
  candidates_sha256: <hex>
  source_sha256: <hex>
  selected:
    - <extracted Lean name>
  declined:
    - name: <extracted Lean name>
      reason: "<why>"
  approver: "Name <email>"
  by: person | agent
  date: YYYY-MM-DD
specification:
  - challenge: <Challenge module>
    spec_digest: <nat>
    approver: "Name <email>"
    by: person | agent
    date: YYYY-MM-DD
```

It carries no per-theorem hash (the registries hold those) and repeats no manifest content.

## Generated files

None carries a timestamp or a commit hash. The four gate outputs and `recheck.txt` name the
**certificate identity** instead, so an unchanged tree regenerates `axioms.txt`, `digests.txt`,
`ladder.txt` and `countermodels.txt` byte for byte. A `../check.sh --core-only` or
`--committed-extraction` run writes none of them (its outputs go to the run's temporary
directory), so an INCOMPLETE pre-check -- whether it left the bridge out entirely (`--core-only`)
or audited it without charon/aeneas (`--committed-extraction`) -- can never be mistaken for the
claim; `../scripts/certificate-identity.sh --check` additionally fails an
`axioms.txt` carrying a NOT AUDITED package section.

### digests.txt
`sha256sum` of every input of a gate run: Rust sources and tests, Cargo files, every Lean module
(Challenge libraries included), the Lake files and toolchain pins, `policy.txt`, `candidates.txt`,
`vectors.txt`, the gate's scripts, the `../recheck/` pins, and, at the root, `flake.nix`,
`flake.lock`, `rust-toolchain.toml`, `nix/comparator.nix`, `nix/lean-toolchain-bin.nix`,
`nix/landrun.nix`, `nix/aeneas-pin.json`, `nix/aeneas-prebuilt.nix` and `nix/mir-sysroot.nix`,
followed by `identity: sha256:<hex>`. This is the G5 evidence. The file list lives once, in
`../scripts/certificate-identity.sh`. `Cargo.toml` and `Cargo.lock` are the one exception to plain
`sha256sum`: both are digested through the same version-normalized view `source_sha256` uses (see
Select, above), via `cargo_version_normalized_sha256` in `../scripts/lib/approval-digests.sh` --
the root package's own `version` is excluded, everything else in either file is hashed verbatim.

The certificate identity is the sha256 of the digest lines exactly as written; from
`framed_channel/`:

```
grep -vE '^(#|identity:)' certificate/digests.txt | sha256sum
```

It covers inputs only. Excluded are the generated files (nothing hashes itself), `approvals.yaml`
(covering it would make every approval invalidate the certificate it approves), and prose: the
manifests, `shared.yaml`, and the README files. Each is hand-edited prose that can be revised for
clarity, restructured, or have a typo fixed without re-running the evidence it describes;
digesting it would force a `recheck.txt` re-adopt on every wording fix, for no verification
benefit. The consequence for a reader comparing two certificates: equal identities mean equal
evidence inputs, never equal manifest prose -- read the manifests and README themselves for that.
`rust-toolchain.toml` IS included, unlike the other root-level file it sits beside: the flake
reads it directly as a local file (`builtins.readFile` in `flake.nix`), so `flake.lock` does not
cover a change to it the way it covers every other pinned input. A manifest's `toolchain.shared:` points at `shared.yaml`, whose own
`toolchain.certificate_identity:` is a pointer to `digests.txt`, not a value. The gate computes
the identity before its first stage and fails if the
tree changed by the end. `bash ../scripts/certificate-identity.sh --check` (no build, no network) compares
the tree's identity with the one every generated file names.

### axioms.txt
The Lean version, the certificate identity, the trusted axiom set, the flagged allow-list, and every
`#print axioms` record from the build, grouped by package (`core` for `../lean`, `bridge` for
`../aeneas`) and module. A package whose stage was skipped is named as not audited. The G0 evidence.

### ladder.txt
One proof-ladder record per registered core theorem, `<declaration> <method> [qualifier]`, with a
header explaining the rung order, `manual`, `instance` and the post-declaration qualifier, and a
per-method summary. Each record is made by `../lean/FramedChannel/Ladder.lean` where the theorem is
declared, so the method recorded is the method of the proof the build checks. Bridge rows are not
laddered, and the file says so. See `../README.md`, "Proof ladder".

### countermodels.txt
One record per rejected candidate statement refuted in
`../lean/FramedChannel/Evidence/Countermodels.lean`, `<candidate> <witness>`. The witness is read
by `refuted%` off a kernel-checked search theorem, never typed by hand.

### candidates.txt
The Select candidate set described above, written by `../scripts/refresh-candidates.sh`. Byte-stable; the
gate's extraction-staleness stage regenerates it from the same charon LLBC and fails on a
difference.

### vectors.txt
Written by `../scripts/refresh-vectors.sh`, which runs `lake env lean --run GenVectors.lean` in
`../aeneas/`: it evaluates the Charon/Aeneas extraction of `../rust/src` (both queue records, the
codec, the checksum, the frame codec and `Channel<Q>` at both queues) and prints (input, output)
records carrying the Rust results themselves: error variants, `Some`/`None`, consumed counts.
`../rust/tests/differential.rs` reads it with `include_str!` and compares the compiled Rust against
it. The header records only the Lean version, the Aeneas revision and the platform's `usize`
width, so a non-empty diff means a translated behavior changed.

`../check.sh` never writes it, so the gate cannot quietly repair what it guards; its
differential-vectors stage regenerates into a temporary file and diffs, and every changed record
should be read before it is accepted. That stage needs the bridge package; without it the vectors
are reported NOT CHECKED and are tied to the Rust by `cargo test` alone.

This is finite testing on fixed vectors, not a proof: agreement is evidence about the translation
(rustc MIR, Charon, Aeneas) on the recorded inputs and, through the bridge theorems, about the
models on the same inputs. It says nothing about other inputs, release-profile arithmetic or the
Lean interpreter that computed the values, which is why every verdict it supports is `validated`
(G1, G2, G4).

### recheck.txt
Written only by `../check.sh --recheck`, and always over both packages (`--core-only --recheck` is
refused). It names the certificate identity and is **current** only
while that equals the identity in `digests.txt`; a plain run (no `--recheck`) never rewrites it
and reports one of four outcomes: STALE (its identity does not match the tree's), current but
recording a `FAIL` verdict, current but `record:` not `complete` (PARTIAL, not a pass), or current
and a pass (`[ok]`, with the OK/EXPECTED-REJECTION and NOT-RUN verdict counts). A stale record is
a note, not a failure, and establishes nothing for the tree it
does not name. It contains no wall times and no temporary room paths, but it does record tool
locations (nix store paths, and library paths the sandbox grants), so it is stable on one machine
rather than across machines. Sections:

- **`produced on:`**: `<uname -s> <uname -m> (<producer>)`, where `<producer>` is
  `${RECHECK_PRODUCER:-local}` -- `local` from a contributor's own machine, or
  `CI: verify.yml recheck job` from `.github/workflows/verify.yml`'s `recheck` job, which sets
  the environment variable. No run ID or URL: that would break byte-stability of the record for
  one identity across re-runs on the same host; the run's URL travels with the CI-uploaded
  `recheck-record` artifact instead (see below) and is printed by
  `../scripts/adopt-recheck.sh`;
- **`record:`**: `complete` when every verdict below is accounted for (no verdict is `NOT-RUN`
  other than `lean4lean-fresh`'s: that line is always emitted, but its verdict is `NOT-RUN`
  unless `check.sh --recheck-fresh` requested it, and a `NOT-RUN` there alone still counts as
  complete), computed by
  `../scripts/lib/recheck-revs.sh`'s `recheck_record_completeness`. A run whose record is not
  complete -- Comparator `NOT-RUN` on a non-Linux host is the common case, but a Linux host
  missing `landrun`/`systemd-run --user` is partial too -- is written instead to the gitignored
  `recheck.partial.txt`, headed with a `PARTIAL RECORD` banner comment, and the committed
  `recheck.txt` is left untouched: **a partial record can never be mistaken for a complete one**,
  mechanically, not just by convention. Defense in depth: `../scripts/certificate-identity.sh
  --check` `[FAIL]`s a committed `recheck.txt` that names this tree's identity but lacks
  `record: complete` (catching a hand-copied partial), and a plain `check.sh` run reports such a
  file `[skip] ... PARTIAL, not a pass` rather than `[ok]`;
- **tool revisions**: the Comparator build and its in-process kernel Lean version, lean4export
  and Lean4Lean as built in `../recheck/` on the project's Lean, leanchecker, landrun;
- **revision coherence**: `../scripts/lib/recheck-revs.sh`'s lines (a `[FAIL]` stops the run first);
- **sandbox deviations**: the grants `../recheck/landrun-shim.sh` adds to Comparator's own landrun
  arguments, per room: `TMPDIR` inside the room's `.lake` (for `bv_decide`'s SAT files), execute
  on git's shared libraries (without it Lake deletes a package it cannot identify), execute on
  the ELF interpreter the toolchain's `lake` requests (on NixOS, nix-ld), and, in the
  bridge room, write access to `<room>/lean/.lake` (the path dependency's build directory).
  `--env CI=...` appears where the recheck ran with `CI` set (every hosted runner): Aeneas's
  lakefile precompiles its `AeneasMeta` library only where `CI` is unset, each room elaborates
  the lakefiles afresh, and Comparator's sandbox drops the variable, so without it a room
  configures the read-only linked Aeneas package differently from the tree that built it and
  Lake tries to rebuild it in place. It grants nothing; a host without `CI` has no such line.
  One line is not a grant: `PATH: lake is <toolchain>/bin/lake.orig` appears where the toolchain
  was installed by nixpkgs' elan (the dev shell's, so every hosted runner), which replaces `lake`
  with a bash wrapper around the release binary. Comparator's sandbox grants no execute on a
  shell, so the rooms resolve `lake` to the wrapped binary instead of widening the sandbox to
  one; a toolchain installed by upstream's elan has no wrapper and no such line;
- **hardening**: `systemd-run --user` without AF_UNIX sockets; an outer `landrun --best-effort`
  confining every process to writes inside its room and no network; a before/after check of the
  fetched packages the bridge room links read-only. Best-effort is required, not a convenience --
  see [`../recheck/README.md`](../recheck/README.md)'s Landlock/ABI-V9 explanation for why and
  what is probed on the running kernel -- and a failed probe is a `FAIL`, never an unsandboxed
  run. This outer layer grants read and
  execute on the whole tree (`--rox /`), read-write on `/dev` (`--rw /dev`, needed by the build
  tools it launches), and read-write-execute on the room itself -- what may be executed inside a
  build is restricted by Comparator's own sandbox, nested inside it. The bridge room's `aeneas/`
  packages (Aeneas, Mathlib, linked read-only, never copied) are hashed before and after the run;
  a change is a `FAIL` -- a build that wrote into a dependency it is only supposed to read is not
  the recheck this repository claims, sandbox or not. `../check.sh --recheck` runs the systemd-run
  and outer-landrun probes once per invocation (memoized in `../scripts/lib/recheck-revs.sh`'s
  exported `RECHECK_PROBE_*` variables) and the two child scripts that share this section's
  contents inherit that result rather than re-probing; a standalone run of either script probes
  fresh;
- **Comparator's six assumptions**, with how each was met. `recheck.txt` records only the two that
  carry run-derived data -- **binaries** (the checked revisions, cross-referenced against "tool
  revisions" above) and **kernel** (the in-process Lean kernel version and the toolchain the
  lean4export export was built from) -- and points here for the other four, which never vary run
  to run:
  - **trusted imports**: each Challenge module imports only the allow-only definitions layer
    (`../check.sh`'s `LAYER_ALLOW_RULES`, its "layer import rule" stage), Aeneas and its own
    modules; each room is populated from the digested file list of the run's certificate identity,
    and its digests equal the source tree's; the bridge room's Aeneas and Mathlib are the
    project's own fetched, lake-manifest-pinned packages, linked read-only;
  - **no prior compilation**: one fresh room per config (core, each flagged row, bridge), run
    exactly once; no `.lake` of the source tree is reused, except the fetched dependency packages
    the trusted-imports assumption above already accounts for;
  - **landrun**: Landlock enforcement is probed on the running kernel, not assumed (a write under
    `--ro /` must be denied, a TCP connect with no grant must fail with `EACCES`; see "revision
    coherence" above); landrun's own correctness -- that a probe passing means every other grant
    it enforces is correctly enforced too -- is trusted, not independently checked;
  - **privilege**: the recheck does not run as root (Comparator assumes an unprivileged user; a
    root run would bypass filesystem permissions the sandbox and the room both rely on).

  A run in which Comparator produced no verdict at all (every config `NOT-RUN`, e.g. every macOS
  run: Comparator needs Landlock) states these six as the design the record would have checked,
  not as a run's own findings; `recheck.txt` itself says so inline, next to the verdicts.
- **verdicts**, one per Comparator config and per kernel checker and package.

What each verdict establishes, and what it does not:

| Checker | Verdict | Establishes | Does not establish |
|---|---|---|---|
| Comparator, `core` / `bridge` | `OK` | for every registered name except a flagged row: the statement equals the Challenge module's, the proof uses only the trusted axioms, and Comparator's in-process kernel accepts the lean4export export of the build, in a fresh room, conditional on the six assumptions and the recorded deviations | that the Challenge says the right thing (G4); landrun's correctness; independence from the C++ kernel |
| Comparator, `flagged-<decl>` | `EXPECTED-REJECTION` | rejection with exactly `Illegal axiom detected: '<its bv_decide helper>'`; since Comparator compares statements before axioms, the statement equals the Challenge's | kernel acceptance of that proof (the axiom check stops the run first). A pass would be a FAIL |
| Lean4Lean, `core` / `bridge` | `OK` | every declaration the package's modules add (Challenge libraries included) re-typechecked by a Lean-in-Lean kernel | independence (Lean4Lean is derived from the C++ kernel); imports (Init, Std, Aeneas, Mathlib); any axiom policy |
| Lean4Lean, `lean4lean-fresh core` | `OK` with `--recheck-fresh`, else `NOT-RUN` | the same over the core registry's whole import closure, from Init | as above, except imports |
| leanchecker, `core` / `bridge` / `leanchecker-fresh core` | `OK` | a same-kernel replay of the modules from their `.olean` files (fresh: the core closure from Init) | any independence: it is the kernel that built the project |

`NOT-RUN` (a tool or build absent, or no bridge package) establishes nothing and is never reported
as passed; `FAIL` fails the run. nanoda, Comparator's external kernel, is not built, so no check by
a kernel independent of the C++ kernel is claimed.

**Platform**: the kernel replay (Lean4Lean, leanchecker) needs no sandbox and runs
on any platform with the pinned Lean toolchain, including macOS;
Comparator needs a Landlock sandbox, a
Linux kernel feature, and is `NOT-RUN` with reason "Landlock sandbox is Linux-only" everywhere
else. See `../recheck/README.md`'s "Prerequisites not pinned here" for the full platform matrix,
the macOS behavior (a local run there can only ever write the partial file above), and why a
macOS-native Seatbelt sandbox for Comparator was considered and not built.

**CI is the producer of the canonical record.** `.github/workflows/verify.yml`'s `recheck` job's
x86_64-linux leg (`ubuntu-24.04`) runs the full gate for real, sets `RECHECK_PRODUCER` so
`produced on:` names it, and uploads `certificate/recheck{.partial,}.txt` as the `recheck-record`
artifact on every run (`if: always()`, 14-day retention) -- so the record is inspectable even when
the gate failed before or during the recheck stage. Any contributor, including on macOS or a Linux host without
Landlock, obtains a complete record locally with:

```
gh workflow run verify.yml --ref <branch>
bash scripts/adopt-recheck.sh          # downloads the latest matching run's artifact,
                                        # validates it, and copies it to certificate/recheck.txt
git add certificate/recheck.txt && git commit
```

`adopt-recheck.sh` refuses a candidate whose identity does not match this tree, that is not
`record: complete`, or that carries a `FAIL` verdict -- printing the specific reason -- and never
runs `git add`/`git commit`/`git push` itself. It is not a certificate-identity input.

**Comparator configs.** `../scripts/comparator-configs.sh` derives them, never committed: per package the
Challenge library root as `challenge_module`, the registry as `solution_module`, the registered
names minus the `flagged` rows as `theorem_names`, and the `trusted` rows of `policy.txt` as
`permitted_axioms`. There is no `definition_names` field at all: every definition a statement mentions is imported
unchanged by both sides from the definitions layer and approved through `spec_digest`. The two
shared-proof rows are in `theorem_names` but not restated; both sides import the same proved
constants. No statement closure reaches any other proof, so the two packages' configs are
independent.

**Why the flagged row is an expected rejection.** Each `flagged` row gets its own config with the
same `permitted_axioms` and an `.expect` file naming its `bv_decide` helper axioms. The helper
cannot be permitted instead: Comparator exports permitted axioms from the Challenge too, and the
statement-only Challenge has no such constant, so lean4export would fail before anything is
compared. The rejection still proves the statement matches; the row's kernel twin,
`crc8_step_linear_kernel` (same statement), is checked in the main core config.

## The asymmetries that are deliberate

A certificate reader comparing two units will find places where they are not symmetric. Three of
them are on purpose, and each is stated where it belongs rather than left to be rediscovered:

- **Only queues have a simulation structure.** `Bridge/Queue/`'s `QueueSim`, extracted carrier and
  six transport theorems exist for queues and for nothing else. The rule that decides this --
  a simulation structure is for an interface the Rust dispatches through a trait AND that a
  composite is proved generic over, which `BoundedQueue<T>` is and no other interface in the crate
  is -- is stated in full in `../aeneas/README.md`, "The canonical bridge pattern". No `CodecSim`
  or `ChecksumSim` is owed. Varint and Crc8 instantiate their laws directly, and Crc8's two
  implementations are two functions proved to agree, not two impls of a trait.

- **`channel.new_idle_RB` versus `channel.with_queue_idle_VQ`.** The two idle-constructor rows are
  not spelled the same because they are not about the same constructor: `Channel::new` is concrete
  (it builds a `RingBuffer<Vec<u8>>`), while `Channel::with_queue` takes any queue and is what the
  second queue is reached through. Making the names match would make two different claims look
  like one.

- **Two `Registry.lean` files.** One per Lake package, split exactly at the Aeneas/Mathlib
  dependency: `../lean` must stay free of both (`../check.sh`'s layer rule enforces it), so the
  core rows cannot live beside the bridge rows. `allItems`/`allBank` in the bridge registry
  concatenate the two, and the gate checks the combined totals, so nothing is lost by the split.

Everything else about the units is meant to be symmetric, and where it was not, it was made so:
both queue bridges now register the same claims, and core registers both of its `ChecksumLaws`
instances as the bridge registers both of its extracted ones.

## What the gate enforces

`../check.sh` runs its stages in the order `--help` lists and fails, naming the offending
declaration or file, on any of the following. The gate fails (exit 2) before building anything
when charon, aeneas or jq is absent; only under `--core-only` (bridge left out entirely) or
`--committed-extraction` (bridge audited against the committed extraction, charon/aeneas never
invoked) do the stages that need charon/aeneas skip with a note, and then a skipped check is
reported NOT CHECKED or UNAUDITED, never passed, and the run ends INCOMPLETE (exit 3), never PASS.

**Revisions and staleness.** `../scripts/lib/aeneas-revs.sh`'s `aeneas_rev_coherence`:
- `lean/lean-toolchain` and `aeneas/lean-toolchain` disagree;
- disagreeing Aeneas revisions among `../../nix/aeneas-pin.json`'s `rev`, `flake.lock`'s locked
  aeneas revision, `../aeneas/lake-manifest.json`'s aeneas package revision, and (when on PATH)
  `aeneas -version`;
- `charon version` (when on PATH) disagreeing with `../../nix/aeneas-pin.json`'s `charon_rev`;
- when the fetched checkout under `aeneas/.lake/packages/aeneas` is at the pinned revision: its
  own `charon-pin` disagreeing with the pin file's `charon_rev`, or its `lean-toolchain`
  disagreeing with ours (a checkout at a different revision is a `[skip]`, never a `[FAIL]`, since
  a cached or not-yet-updated checkout is mutable state, not a pinned input);
- under `check.sh --committed-extraction`, the `--no-binaries` variant skips the `aeneas`/`charon`
  binary comparisons entirely (whatever happens to be on PATH is not that run's input) rather than
  comparing them;
- separately, a committed extraction or `candidates.txt` that differs from what charon/aeneas
  produce from today's `../rust/` (when they are on PATH).

**Policy.** A row in `policy.txt` whose first field is not `trusted`, `flagged` or
`shared-proof` (blank lines and `#` comments aside).

**Layer import rule.** A Lean module importing across a forbidden edge: a specification importing
a model, a composition or the ladder tooling; a model importing a composition; the generic channel
importing a queue model; anything in `../lean` importing Aeneas or Mathlib; a proof module,
registry or generator importing a Challenge; anything importing an Evidence module; a definitions
module importing anything but specification, definitions or extraction modules (the allow rule
also permits `Std.Tactic.BVDecide`, bundled with the toolchain, for the one bit-vector obligation);
a Challenge module importing anything but those, Aeneas and Challenge modules.

**License headers.** A hand-written source file without `SPDX-License-Identifier: Apache-2.0` in
its first lines, an Aeneas-generated file without its generator banner, or a missing `LICENSE` or
`NOTICE` (`../scripts/check-spdx.sh`).

**Per package (core, then bridge).**
- a declaration that uses `sorry`;
- a bare `native_decide`, which is prohibited outright;
- a bare search tactic (`exact?`, `apply?`, `try?`, `grind?`, `+suggestions`): a committed proof
  carries what a search found, never the search;
- a `rung` that is not the whole proof of its declaration;
- a vacuous definition (a body that is trivially true);
- in the bridge package, an `axiom`, `sorry`, `admit` or `native_decide` in
  `Extracted/FunsExternal.lean`;
- an expected Aeneas-generated `.lean` file (in the bridge package's extraction output) that does
  not exist;
- a module carrying `#print axioms` whose record Lake's replayed build log does not capture, even
  after a from-scratch rebuild.

**Registry statement hashes.** A row whose statement hash is stale, in either registry.

**Specification consistency.** A Challenge library that is not statement-only (no definition, axiom
or proof); a `sorry` warning from anywhere but a confirmed Challenge statement; restated names that,
with the shared-proof rows, differ from the registered names; a restated statement hash that differs
from the registry column; or a proof inside the definitions layer, or reached by a statement, that
is not a shared-proof row.

**Selection consistency.** A malformed `candidates.txt`; with the bridge package, a registered
statement about an excluded item, or a non-derived in-subset candidate that no registered statement
is about.

**Differential vectors.** A regenerated `vectors.txt` that differs from the committed one, or
`aeneas/GenVectors.lean` emitting any compiler message (a warning or a `sorry`) while regenerating
it (bridge package only).

**Axiom audit.** An axiom outside `{propext, Classical.choice, Quot.sound}`, or a compiler-trusting
axiom (`Lean.ofReduceBool`, `Lean.trustCompiler`, or the native helper
`<decl>._native.bv_decide.ax_<n>_<m>`) for a declaration not on the flagged allow-list, which holds
exactly `FramedChannel.Crc8.crc8_step_linear`. The bank aggregates (`FramedChannel.items` and
`FramedChannel.bank` in the core package, `FramedChannel.Bridge.allItems` and `allBank` over both)
splice every row's proof into one definition, so they inherit the flagged row's axioms by
construction; they are excused for those axioms alone, and still catch a registered theorem that
depends on something it should not; a flagged row with no axiom record at all (remove its
`policy.txt` row); a bank aggregate with no axiom record (remove it from the check's own
aggregate list); a flagged row declared inside an Evidence module.

**Proof ladder.** Ladder records that do not name exactly the core registry's rows, one each;
post-declaration records that differ from the core shared-proof rows; `bv_decide` records that
differ from the `flagged` rows or from the declarations whose axiom record is compiler-trusting;
or a countermodel whose search or refutation theorem is not kernel-only. (A mislabeled or undercut
rung already fails the build.) Bridge rows are reported NOT CHECKED, but the bridge package
emitting any proof-ladder record at all -- only the core registry is laddered -- is itself a
failure; so is an unrecognized ladder method or qualifier, and a countermodel candidate with no
axiom record in an Evidence module.

**Manifest cross-check.**
- the `proofs:` names across all manifests differ from the registered names, in either direction,
  or a name is under both `proofs:` and `supporting:`;
- a `proofs:` or `supporting:` name has no record in `axioms.txt`;
- a manifest lacks a `specification:` block, names a non-Challenge module there, or certifies a
  name not restated in one of those modules (shared-proof rows excepted);
- `certificate/shared.yaml` is missing, lacks `toolchain.certificate_identity:`, names a
  `repository_commit:`, or lacks a `trust.G0_checker.independent_recheck` block with
  `comparator`, `lean4lean` and `leanchecker` entries, each with a verdict and
  `record: certificate/recheck.txt`;
- a manifest's `toolchain:` lacks `shared: certificate/shared.yaml`, its
  `trust.G0_checker.independent_recheck:` lacks that same `shared:` line or restates a
  `comparator`, `lean4lean` or `leanchecker` entry of its own, or it names a `repository_commit:`;
- a manifest or `shared.yaml` restates a toolchain revision: the revision-token lint fails on any
  hex revision (7-40 hex characters, with at least one digit and one letter) or version triple
  (`vN.N.N`, optionally `-rcN`) outside a `#` comment.

A name owned by a skipped package (ownership read from the registries and sources, never from a
namespace prefix) is reported UNAUDITED, neither passed nor failed.

**Independent recheck.** With `--recheck`, any `FAIL` verdict; otherwise the stored record is
reported as one of four outcomes -- STALE, current with a `FAIL` verdict, current but PARTIAL, or
current and a pass -- never as an outcome of this run itself.

**Rust.** A `cargo fmt --check` diff, a `cargo clippy --all-targets -- -D warnings` warning, or a
failing `cargo test` (skipped with `--lean-only`).

**Certificate identity.** An input that changed during the run.

**Approvals (last).** An absent `approvals.yaml`; a parse error (only the fixed shape
`../scripts/lib/approval-digests.sh` documents is accepted -- any other key, indentation or list
form fails); a name listed more than once under `selected` or `declined`; a declined name with an
empty reason; a record whose `by:` is not `person`/`agent`, or whose `by:` and approver-name form
disagree (an agent approver is named `Name (agent) <email>`; a person's is not); a selection whose
`source_sha256` or
`candidates_sha256` is not today's, whose selected and declined lists overlap or do not together
equal the in-subset candidates, or (with the bridge package) whose selected list is not exactly the
in-subset candidates the registered statements reach; not exactly one record per existing Challenge
module at today's `spec_digest`; or a record without an approver of the form `Name <email>` and a
real date. On a stale digest it names the commit that recorded the approved one and prints the diff
since. Every other stage has passed by then, so a run red only here means "not yet
(re-)approved".

## Regenerating

The writers of the generated files, and the other entry points, are listed in `../README.md`,
"Running the checks"; `../scripts/recheck-comparator.sh` and `../scripts/recheck-kernel.sh` run the two halves of
the recheck alone, and `../scripts/recheck-record.sh` renders their combined output into
`recheck.txt`/`recheck.partial.txt` (the same renderer `../check.sh --recheck` uses). Every script
accepts `--help`, which gives its exact exit codes: 0 pass, 1 a
check failed, 2 usage error or missing prerequisite, and, for `../check.sh` under `--core-only` or
`--committed-extraction`, 3 (pre-check complete, INCOMPLETE -- not the verification claim).

## Navigation

- [Parent Directory](../README.md)
