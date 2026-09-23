# Trust model

This page states what a green badge, a green `full-gate.sh` run and a valid certificate do and
do not certify. It is written for a reader who wants to judge the result without reading Lean or
workflow YAML.

## What a green result means

Three different things can be green, and each certifies something different:

- **The CI badge** ([ci.yml](../.github/workflows/ci.yml)) means the flake's Linux build/test/lint
  path passed, and the repository's shell scripts and workflow YAML are syntactically sound. It
  says nothing about the proofs.
- **The Verification badge** ([verify.yml](../.github/workflows/verify.yml)) means the committed
  certificate under `framed_channel/certificate/` matches what a fresh gate run over the current
  tree on `main` produces, and the independent recheck of that tree is complete and passes, on
  x86_64-linux and aarch64-linux. See [ci.md#platform-matrix](ci.md#platform-matrix) for why other
  platforms are not part of this badge.
- **Exit 0 from `bash full-gate.sh --yes`** on your own machine means the gate you just ran passed.
  The gate's pre-check modes (`--core-only`, `--committed-extraction`) end `INCOMPLETE` (exit 3) by
  design and are never the verification claim; only exit 0 from a real gate run is.

A badge describes the **latest run of that workflow on `main`**, not your own checkout and not a
certificate committed in your own tree — a stale local clone or an unadopted recheck record does
not turn the badge red. See [Check it yourself](#check-it-yourself) below for how to confirm your
own tree, not just the badge.

## Verified, asserted, and not run, per platform

This table summarizes [ci.md#platform-matrix](ci.md#platform-matrix), which is the canonical,
mechanical detail (job names, triggers, workflow files). Support level is what
`bash full-gate.sh --support-level` resolves for that system at the current pin.

| OS | Verified | Asserted but not independently verified | Not run |
|---|---|---|---|
| x86_64-linux | Full gate (`check.sh --aeneas`); the committed certificate matches a fresh gate run (certificate freshness); the complete independent recheck (kernel replay plus Comparator). This is where the canonical certificate and recheck record are produced. | — | — |
| aarch64-linux | Full gate (`full-gate.sh --yes`); the committed certificate matches a fresh gate run here too, byte-for-byte modulo the host triple; the complete independent recheck. | — | — |
| aarch64-darwin | Full gate (`full-gate.sh --yes`); the kernel replay (Lean4Lean, leanchecker) runs for real here. | — | Comparator — reported `NOT-RUN`, reason "Landlock sandbox is Linux-only"; the recheck record here is therefore partial by design, never adopted as the canonical `certificate/recheck.txt`. |
| x86_64-darwin | A fresh clone installs (`install.sh`); `check.sh --committed-extraction` audits both packages against the committed extraction. | — | `full-gate.sh`; the substituter probe; the independent recheck — nothing here certifies the proofs. |

**The non-Nix path** (`docs/setup-without-nix.md`) is not a fifth row here for the same reason it
is not a fifth row of the Platform matrix: it exercises only the elan/Rust install procedure and
`check.sh --committed-extraction`, with no Nix invocation, no full gate, and no recheck.

## Worked example: the x86_64-darwin canary leg

[fresh-clone-canary.yml](../.github/workflows/fresh-clone-canary.yml) replays the documented
fresh-clone user path: the monthly schedule covers its two Linux legs only, and the x86_64-darwin
leg this section is about runs only when requested with `-f macos=true` (see
[ci.md#macos-runs-on-request-only](ci.md#macos-runs-on-request-only)). On x86_64-darwin, a green
leg there certifies exactly two things: that a fresh clone installs, and that
`check.sh --committed-extraction` passes. `full-gate.sh` and the substituter probe are skipped by
design (`gate=light-only`) — the full gate remains unevidenced on this platform, and a green badge
or a green canary run does not change that. See
[ci.md#known-coverage-gaps](ci.md#known-coverage-gaps) for the fuller account, including why the
platform is light-only at all.

## What the certificate identity covers

The certificate identity is a sha256 over every gate *input*: Rust sources and tests, Cargo files,
every Lean module, the Lake files and toolchain pins, `policy.txt`, `candidates.txt`,
`vectors.txt`, the gate's own scripts, the recheck tool pins, and, at the repository root,
`flake.nix`, `flake.lock`, `rust-toolchain.toml` and the vendored package/pin files under `nix/`.
`rust-toolchain.toml` is included even though `flake.lock` covers every other pinned input, because
the flake reads that one file directly rather than through a lock entry.

It excludes the **generated** files (nothing hashes itself), `approvals.yaml` (covering it would
make every approval invalidate the certificate it approves), and all **prose** — the certificate
manifests, `shared.yaml`, and the READMEs. Prose can be revised for clarity or have a typo fixed
without re-running any evidence.

The consequence for a reader: **equal identities mean equal evidence inputs, never equal manifest
prose.** Read the manifests and READMEs themselves for that. See
[certificate/README.md's Generated files section](../framed_channel/certificate/README.md#generated-files)
for the full file list and the exact recomputation command.

The identity changes on every source edit, so it is a content fingerprint, not a version number:
two trees agreeing on it are the same tree, and nothing more is claimed.

## What the recheck establishes and does not establish

The independent recheck re-derives the same result by a second route: a kernel-in-Lean replay
(Lean4Lean, leanchecker) on any platform, and, on Linux only, Comparator — a sandboxed,
independent statement-and-proof comparison against the approved Challenge specification.

| Checker | A passing verdict establishes | It does not establish |
|---|---|---|
| Comparator | that the proof for each registered name matches the approved statement and uses only the trusted axioms, accepted by an independent, sandboxed kernel in a fresh room, conditional on its stated assumptions and recorded sandbox deviations | that the approved statement says the right thing (that is a human judgment, recorded separately); the correctness of the sandbox itself; independence from the same kernel implementation that built the project in the first place |
| Lean4Lean | that every declaration re-typechecks under a second, independently-implemented kernel | which axioms were used, or anything about the imports (Init, Std, Aeneas, Mathlib) |
| leanchecker | a same-kernel replay of the built `.olean` files | any independence — it is the same kernel that built the project |

Four outcomes are possible for the committed `certificate/recheck.txt`, and only one of them is
a pass over the *current* tree: **STALE** (its recorded identity no longer matches the tree),
**current but a checker reported `FAIL`**, **current but the record is only `PARTIAL`** (some
checker did not run — the expected outcome on macOS), or **current and every checker passed**.

A subtlety worth stating plainly: **`bash check.sh --recheck` exits 0 whether the record it wrote
is complete or only `PARTIAL`.** This is by design — a `PARTIAL` record is the only possible local
result on a non-Linux host, since Comparator is Linux-only, and treating that as a local failure
would make the recheck flag unusable outside Linux. CI's own `verify.yml` recheck jobs add a
separate completeness check on top of `check.sh`'s exit code for exactly this reason, so a green
`verify.yml` recheck job is stronger evidence than a green local `--recheck` run: only CI escalates
a `PARTIAL` record to a job failure.

`verify.yml`'s `recheck` job's x86_64-linux leg is CI's canonical producer of a complete record,
and `framed_channel/scripts/adopt-recheck.sh` refuses to adopt a `--from FILE` record whose
`produced on:` line does not name either that leg or its aarch64-linux twin — a locally-produced
record cannot be smuggled in as the canonical one. See
[certificate/README.md's recheck.txt section](../framed_channel/certificate/README.md#rechecktxt)
for the full outcome table and every deviation the record itself lists.

## Ground classes and verdict words

Every certificate manifest states one verdict per **ground class** — the six places a certificate
can be wrong:

| Class | In plain terms |
|---|---|
| G0 (checker) | Is the proof checker sound, and do the proofs use only trusted axioms? |
| G1 (translation) | Does the Charon/Aeneas translation of the Rust mean what the Rust means? |
| G2 (IR faithfulness) | Do rustc's MIR and Charon's intermediate representation faithfully represent the Rust? |
| G3 (models) | Are the library models the extraction relies on (Aeneas's `Vec`, scalars, and this crate's own externals) right? |
| G4 (specification) | Does the approved statement say what the component should actually do? |
| G5 (binding) | Is the certificate bound to exactly these sources and these statements? |

Every verdict is one of exactly three words: **`verified`** (a machine decided it, and the
decision is reproducible here), **`validated`** (evidence supports it, short of a proof — typically
differential testing), or **`trusted`** (accepted without either, with the reason stated).

Two rules keep those words honest: **`verified` is never applied to a whole component** — the only
component-level `verified` verdict is G5 (binding); the independent-recheck entries for Comparator
and Lean4Lean are `verified` only as *scoped, current-record* claims, not as a statement about the
whole checker class. And **a composite is never more trusted than its least trusted part**: the
composite `Channel` component is exactly as trusted as its weakest input. See
[certificate/README.md](../framed_channel/certificate/README.md#ground-classes-g0-g5) for the
per-component detail and the full enforcement list.

## This repository's CI vs. upstream

Some of what a certificate says rests on evidence this repository itself produces; the rest is
taken on trust from an upstream component this repository did not build.

- **This repository's own evidence**: the scoped, current independent-recheck verdicts (Comparator
  and Lean4Lean, each `verified` only while `recheck.txt` is current); the G5 binding (`verified`
  — the sha256 identity over every gate input); and, more broadly, everything `check.sh` itself
  decided by running the gate on this tree.
- **Taken from upstream, as `trusted`**: the G1 Charon/Aeneas translation step, the G2 faithfulness
  of rustc's MIR and Charon's intermediate representation to Rust semantics, and the G3 library
  models Aeneas ships. None of these three is proved here; each manifest's differential-vector
  evidence (dozens to a few hundred recorded input/output pairs, depending on the component, run
  through both the compiled Rust and the Lean evaluation of the extraction) is real but finite
  testing, `validated` rather than `verified` — it is evidence against a translation fault on the
  recorded inputs, not a proof about every input.
- **Also taken on trust, outside the certificate's own ground classes**: the Nix/nixpkgs supply
  chain (every dependency this repository does not vendor itself), and the Landlock/landrun sandbox
  guarantees Comparator's rooms rely on for isolation, not for correctness of the proof check
  itself.

## Platform tiers

Informally, three tiers exist today: **full gate with a complete recheck** (x86_64-linux,
aarch64-linux); **full gate with a partial-by-design recheck** (aarch64-darwin); and
**light-only, no proof gate at all** (x86_64-darwin). Beneath all four designated systems,
`nix flake check --all-systems` additionally evaluates every dev shell `flake.nix` defines —
including both darwin systems — on every push; this is a lightweight floor, not a fourth tier or
a substitute for any of the three above (recheck completeness — complete vs. partial-by-design —
is an attribute of the full-gate tier, not a fourth tier of its own). How a platform moves between
tiers, or when one is retired, is recorded in [docs/ci.md](ci.md#platform-matrix)'s own notes
where it has come up.

## Check it yourself

A badge or this page states a general property; your own tree's current state is one command away:

```bash
# what tier your own system resolves to, right now, at the current pin
bash full-gate.sh --support-level

# does the committed certificate (and, if present, recheck.txt) name this tree?
bash framed_channel/scripts/certificate-identity.sh --check

# force a fresh Verification run rather than waiting for the next push
gh workflow run verify.yml --ref <branch>

# pull down CI's canonical, complete recheck record and adopt it locally
bash framed_channel/scripts/adopt-recheck.sh
git add framed_channel/certificate/recheck.txt && git commit
```

`certificate-identity.sh --check` is the one command that tells you whether the certificate you
have locally — and, separately, the recheck record you have locally — actually describe the tree
you are looking at, independent of whatever the badge on `main` currently says.
`adopt-recheck.sh` never runs `git add`/`git commit`/`git push` itself; review the diff before
committing. See
[certificate/README.md, "CI is the producer of the canonical record"](../framed_channel/certificate/README.md#rechecktxt)
for the full recipe and what `adopt-recheck.sh` refuses and why.

## Navigation

- [docs/README.md](README.md)
- [docs/ci.md](ci.md)
- [Back to README](../README.md)
