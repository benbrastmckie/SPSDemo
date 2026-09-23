# Continuous integration

Twelve workflows under `.github/workflows/` build, lint, verify and maintain this repository, with four
composite actions under `.github/actions/` that they share:
[`lean-toolchain`](../.github/actions/lean-toolchain/action.yml),
[`mathlib-cache`](../.github/actions/mathlib-cache/action.yml),
[`lake-bridge`](../.github/actions/lake-bridge/action.yml) and
[`substituter-probe`](../.github/actions/substituter-probe/action.yml). This page states what each one runs,
what its green result certifies, and the trigger, cache-budget, cost, timeout and coverage-gap
rationale behind them; each workflow file itself carries a header (often long, restating the same
rationale inline) plus per-step comments, not this level of cross-file synthesis. See
[docs/trust-model.md](trust-model.md) for the summary of what green certifies;
this page remains the mechanical detail it links back to.

**Where the evidence is.** Every "runs on", "passes on" and "reproduces" claim on this page is
asserted by a named job, and the evidence for it is that job's latest run in this repository's
[Actions tab](https://github.com/benbrastmckie/SPSDemo/actions) (and, for the two badged
workflows, the badge on the root README). This page deliberately cites no run or job IDs: an ID
goes stale with the next run, and the Actions tab does not. This repository was published as a
single-commit snapshot of a tree developed in a private repository, where every job described
below ran green on hosted runners; those logs are not public, so a workflow's first run HERE is
its first citable evidence. A schedule- or dispatch-only workflow that has no run listed yet has
simply not been evidenced here yet -- [Known coverage gaps](#known-coverage-gaps) names them.

**Measured figures.** The evidence principle above extends from pass/fail claims to durations,
sizes and ratios. Like a run ID, a measured figure cites no run -- instead it names its job, its
condition (cold or warm, and platform where that varies) and its source: this repository's own
runs, or, where this repository has not yet run that job, the development repository's runs,
labeled as such rather than given this page's own evidentiary voice. A figure that justifies a
committed number (a `timeout-minutes:` budget, a [Cost](#cost) claim) carries an explicit
re-measurement trigger instead of a date, since nothing forces a date to move with the figure it
stamps: re-measure before lowering the budget it justifies, when the job's steps change
structurally, after a toolchain or pin bump for a closure size, or simply by reading the next
monthly canary run or an uncached `no_cache=true` recheck dispatch, both of which already produce
a fresh cold-path timing. A figure that explains a decision without justifying any committed
number -- descriptive color, such as a single observed ratio or per-leg time -- is written as an
explicitly single observation and carries no trigger. A figure governed outside this repository,
such as GitHub's per-OS billing multiplier, is labeled as external policy rather than as something
this repository measured. [Cache strategy](#cache-strategy) already applies this pattern, to
closure sizes and to the glibc interpreter measurement above.

**Concurrency**: every push/pull_request-triggered workflow (`ci.yml`, `verify.yml`,
`setup-without-nix.yml`, `intel-installer-smoke.yml`) keys its
`concurrency:` group on `github.ref` for a push/pull_request run, with `cancel-in-progress: true`,
but on `github.run_id` for a `workflow_dispatch` run of that SAME workflow -- so a manual dispatch
(a manual full `verify.yml` run, a forced full macOS run) gets its own unique
group and never cancels, and is never cancelled by, an ordinary push/pull_request run on the same
ref; two push/pull_request runs on the same ref still cancel-in-progress each other.
`ci-windows.yml`, `ci-macos.yml`, `ci-macos-gate.yml` and `ci-macos-recheck.yml` are dispatch-only
(see [macOS runs on request only](#macos-runs-on-request-only) and "Windows runs on request only"
below), so their group always resolves to the `github.run_id` branch of that same conditional;
`ci-macos-recheck.yml`'s cold, uncached run is just its `no_cache` dispatch input, not a separate
schedule. `update-aeneas-pin.yml`, `update-flake-inputs.yml` and `fresh-clone-canary.yml` use a
single fixed group with `cancel-in-progress: false`: they are schedule/dispatch only, and two
proposal (or replay) attempts must never run concurrently.

## Overview

The root [README.md](../README.md) carries two workflow badges, both GitHub's own status badges
(`https://github.com/<owner>/<repo>/actions/workflows/<file>/badge.svg?branch=main`):

- **CI** -> [ci.yml](../.github/workflows/ci.yml)
- **Verification** -> [verify.yml](../.github/workflows/verify.yml)

A native badge reports the latest run of the WHOLE workflow on `main`; there is no per-job badge.
So every leg of `verify.yml`'s two push jobs -- `verify` and `recheck`, each a 2-leg
x86_64-linux/aarch64-linux matrix -- bears the Verification badge: a red independent recheck turns
it red. Nothing is committed to the repository
to maintain a badge, no workflow holds `contents: write` for one, and no bot commit lands on
`main` between a contributor's fetch and push. The badge URL names the workflow FILE, so renaming
`ci.yml` or `verify.yml` means updating the README in the same commit.

Ten more workflows run but carry no badge; each row below names the workflow, whether it runs on
request or on a schedule/filter, and where to read its full trigger and what-green-certifies
statement (the [Summary](#summary) table, unless a workflow has its own section):

- [ci-windows.yml](../.github/workflows/ci-windows.yml) -- on request only; see [Windows runs on
  request only](#windows-runs-on-request-only).
- [ci-macos.yml](../.github/workflows/ci-macos.yml) -- on request only; see
  [ci-macos.yml](#ci-macosyml-no-badge) below and [macOS runs on request
  only](#macos-runs-on-request-only).
- [ci-macos-gate.yml](../.github/workflows/ci-macos-gate.yml) and
  [ci-macos-recheck.yml](../.github/workflows/ci-macos-recheck.yml) -- on request only; see
  [ci-macos-gate.yml and ci-macos-recheck.yml](#ci-macos-gateyml-and-ci-macos-recheckyml-no-badge)
  below.
- [build-and-test.yml](../.github/workflows/build-and-test.yml) -- a reusable `workflow_call` job
  body, never independently triggered; see
  [build-and-test.yml](#build-and-testyml-shared-job-body) below.
- [setup-without-nix.yml](../.github/workflows/setup-without-nix.yml) -- push/PR, path-filtered to
  the no-Nix procedure's own files; see the [Summary](#summary) table.
- [fresh-clone-canary.yml](../.github/workflows/fresh-clone-canary.yml) -- monthly schedule plus
  `workflow_dispatch`; see the [Summary](#summary) table and [Platform matrix](#platform-matrix).
- [intel-installer-smoke.yml](../.github/workflows/intel-installer-smoke.yml) -- PR-filtered to its
  own file, the one macOS job that still runs automatically; see the [Summary](#summary) table and
  [Timeouts](#timeouts).
- [update-aeneas-pin.yml](../.github/workflows/update-aeneas-pin.yml) and
  [update-flake-inputs.yml](../.github/workflows/update-flake-inputs.yml) -- weekly schedule plus
  `workflow_dispatch`, never on push or pull request; see
  [docs/development.md](development.md#pin-bump-procedure).

## Summary

| Workflow | Trigger | What green certifies |
|---|---|---|
| [ci.yml](../.github/workflows/ci.yml) | push/PR to `main`, no path filter; `workflow_dispatch` | The flake's Linux build/test/lint path is green on x86_64 and aarch64; tracked shell scripts and workflow YAML are sound; every tracked source file carries its license header |
| [ci-windows.yml](../.github/workflows/ci-windows.yml) | `workflow_dispatch` only -- on request (see "Windows runs on request only" below) | The WSL2 setup path (`docs/setup-without-nix.md`'s Windows section) is validated end to end on `windows-2025`: build-and-test.yml's command set runs inside a WSL2 Ubuntu-24.04 distribution with Nix installed there; the `wsl2-probe` job additionally reports (never gates on) whether the recheck prerequisites -- systemd, Landlock -- are usable under WSL2. Not platform coverage: WSL2 resolves to `x86_64-linux`, already covered by the `ubuntu-24.04` leg. |
| [ci-macos.yml](../.github/workflows/ci-macos.yml) | `workflow_dispatch` only -- on request (see [macOS runs on request only](#macos-runs-on-request-only)) | The macOS (aarch64-darwin) build-and-test leg is green, the prebuilt charon/aeneas package runs after its darwin re-sign and reproduces the committed extraction, and the two outside-Nix launchers run under macOS's `/bin/bash` 3.2 on both darwin architectures |
| [ci-macos-gate.yml](../.github/workflows/ci-macos-gate.yml) | `workflow_dispatch` only -- on request | `bash full-gate.sh --yes` passes on aarch64-darwin, as of the last requested run |
| [ci-macos-recheck.yml](../.github/workflows/ci-macos-recheck.yml) | `workflow_dispatch` only -- on request, with a `no_cache` input for an uncached run | The kernel replay (Lean4Lean, leanchecker) of the core and bridge packages is all `OK` on macOS, and every Comparator line is `NOT-RUN` for the documented reason |
| [build-and-test.yml](../.github/workflows/build-and-test.yml) | `workflow_call` only (not independently triggered) | N/A -- reusable job body; see the calling workflow's row |
| [verify.yml](../.github/workflows/verify.yml) | push/PR to `main`, filtered to the gate's inputs; `workflow_dispatch` | The committed certificate under `framed_channel/certificate/` matches what a fresh gate run over the current tree produces, on x86_64-linux and (modulo the host triple) aarch64-linux, and the complete independent recheck passes on both |
| [update-aeneas-pin.yml](../.github/workflows/update-aeneas-pin.yml) | weekly `schedule`; `workflow_dispatch` | N/A -- proposes a pin bump as a PR (or "already current"); certifies nothing itself, since its own in-job gate is not the Verification gate. See [docs/development.md](development.md#how-every-pin-is-proposed) for how this compares with every other pinned dependency's bump mechanism. |
| [update-flake-inputs.yml](../.github/workflows/update-flake-inputs.yml) | weekly `schedule`; `workflow_dispatch` | N/A -- proposes a nixpkgs/rust-overlay relock as a PR, gated in-job by `nix flake check --all-systems` plus a real `full-gate.sh --yes`; opens no PR when that gate fails. See [docs/development.md](development.md#how-every-pin-is-proposed). |
| [fresh-clone-canary.yml](../.github/workflows/fresh-clone-canary.yml) | monthly `schedule` (the two Linux legs only); `workflow_dispatch` (`macos` input adds the two macOS legs) | N/A -- replays the documented fresh-clone user path from scratch (no cache) on every designated OS in the run and fails loudly on an unexpected from-source build, a missing asset, or a hash mismatch; see the [Platform matrix](#platform-matrix) below |
| [setup-without-nix.yml](../.github/workflows/setup-without-nix.yml) | push/PR to `main`, filtered to `docs/setup-without-nix.md`/`nix/aeneas-pin.json`/`rust-toolchain.toml`/`framed_channel/check.sh`/`framed_channel/{lean,aeneas,rust,scripts,certificate}/**`/itself; `workflow_dispatch` | N/A -- narrow coverage of [docs/setup-without-nix.md](setup-without-nix.md)'s documented no-Nix procedure (elan, the runner's own Rust toolchain, `check.sh --committed-extraction`); no full gate, no Charon/Aeneas install, no recheck |
| [intel-installer-smoke.yml](../.github/workflows/intel-installer-smoke.yml) | PR to `main`, filtered to its own file; `workflow_dispatch` -- the one macOS job that still runs automatically (see [macOS runs on request only](#macos-runs-on-request-only)) | N/A -- asserts only that the pinned `nix-installer-action` still installs a working x86_64-darwin Nix, so that an Action-SHA bump which ends Intel support fails on its own PR instead of at the next requested canary. No build, no gate (its first run here completed in 1m32s); see [Known coverage gaps](#known-coverage-gaps) for the sunset decision behind it |

## Trigger policy

Two kinds of workflow run on an admitted push, and the difference is deliberate. (`ci-macos.yml`,
`ci-macos-gate.yml`, `ci-macos-recheck.yml` and `ci-windows.yml` are neither: see [macOS runs on
request only](#macos-runs-on-request-only) and "Windows runs on request only" below -- they run
only when dispatched.)

**Unfiltered** (`ci.yml`): jobs whose input is the whole tree. `check.sh
--core-only` scans every tracked file for a license header, and the build legs compile the Lean
core and test the Rust crate. No positive `paths:` list short of "everything"
would be complete, so there is none, and a documentation-only push still runs it.

**Filtered to their complete inputs** (`verify.yml`,
`setup-without-nix.yml`, and, narrowly, `intel-installer-smoke.yml`): jobs whose verdict depends on
a bounded, enumerable set of files. Each has a positive `paths:` list, with the reasoning for every
entry in the workflow's header; `verify.yml` and `setup-without-nix.yml` carry an identical list on
their `push` and `pull_request` triggers, while `intel-installer-smoke.yml` carries its (single-entry)
list on `pull_request` only, since it has no `push` trigger. GitHub Actions has
no per-job `paths:` filter
-- the filter applies to the whole workflow file -- so a workflow-level list must be the union of
every job's inputs in that file; a single-job workflow must not be filtered by copy-pasting a
multi-job file's list wholesale, or it will admit changes none of its own jobs reads.
`ci-macos-gate.yml` and `ci-macos-recheck.yml` keep their own `paths:`-shaped input lists too (see
the table below), but those lists no longer gate a `push` or `pull_request` trigger -- both
workflows carry `workflow_dispatch` only -- so today they document each job's complete input set
for the maintenance rule below, not an active filter.

| Workflow | `paths:` | Why that is complete |
|---|---|---|
| `verify.yml` | `flake.nix`, `flake.lock`, `nix/**`, `rust-toolchain.toml`, `full-gate.sh`, `framed_channel/**` except `framed_channel/tests/**`, `.github/actions/**`, the workflow's own file | The environment, the launcher, and the gate with everything it reads, unioned across both matrix jobs (`verify` and `recheck`, each an x86_64-linux/aarch64-linux leg pair) -- `recheck`'s two legs pass `--recheck` and so need `framed_channel/recheck/**`. `check.sh` never reads `framed_channel/tests/**`; those fixtures run in `ci.yml` on every push. |
| `ci-macos-gate.yml` | `verify.yml`'s list minus `framed_channel/recheck/**` | Its one job, `aeneas-gate`, runs `bash full-gate.sh --yes` with no `--recheck`, so it never reads anything under `framed_channel/recheck/` (the lean4lean/lean4export tool package); macOS coverage of that stage is `ci-macos-recheck.yml`'s job. If `aeneas-gate` ever starts passing `--recheck`, this row's exclusion must be dropped and the list restored to match `verify.yml`'s. |
| `ci-macos-recheck.yml` | `flake.nix`, `flake.lock`, `nix/**`, `rust-toolchain.toml`, `framed_channel/{lean,aeneas,recheck,scripts}/**`, `framed_channel/certificate/{policy,axioms}.txt`, `.github/actions/**`, its own file | What is replayed, what replays it, what `comparator-configs.sh` reads to decide the `NOT-RUN` lines the job asserts, and everything `flake.nix` reads to evaluate the `.#build` shell. |
| `intel-installer-smoke.yml` | its own file, and nothing else -- the one row in this table still gating a live `pull_request` trigger, per [macOS runs on request only](#macos-runs-on-request-only) | The lightweight exception to the "heavy jobs" framing above -- filtered for precision, not for cost. Its job reads nothing from the tree: it installs Nix and asks Nix what system it is on. Its only input is the action pin it carries, which lives in this file, and Dependabot's grouped PR edits every file holding that pin. Listing anything further would admit changes the job does not read. |
| `setup-without-nix.yml` | `docs/setup-without-nix.md`, `nix/aeneas-pin.json`, `rust-toolchain.toml`, `framed_channel/check.sh`, `framed_channel/{lean,aeneas,rust,scripts,certificate}/**` except `framed_channel/tests/**`, its own file | Its one job installs elan and uses the runner's own Rust toolchain (no Nix), confirms the pinned Aeneas release asset still resolves, then runs `check.sh --committed-extraction` -- which builds and audits both packages (core and bridge) against the committed extraction as-is, skipping only the extraction/candidate staleness check. The list is narrower than `verify.yml`'s: no `nix/**`, `flake.nix`/`flake.lock` or `full-gate.sh`, since this job never invokes Nix or regenerates the extraction from Charon/Aeneas. |

One input of the gate lies outside its list: `check.sh`'s license-header stage reads every tracked
source file. `ci.yml`'s `hygiene` job runs that same check (`framed_channel/scripts/check-spdx.sh`)
on every push, so a header regression in a fixture, or in any other file outside that list, is
caught on the push that introduces it, by the workflow that is never filtered.

**A filter that misses a real input silently weakens the gate**, so the rule for maintaining them
is: when the gate, the replay, or a script either one runs starts reading a new path, add that
path to every list in the table above (both the `push` and the `pull_request` copy) in the same
commit. Directories are listed whole (`framed_channel/scripts/**`, `nix/**`, `.github/actions/**`)
rather than file by file for that reason: a newly sourced helper is covered without anyone
remembering to list it.

**Every filtered Linux workflow keeps `workflow_dispatch` as the "force a full run" path,
alongside its push trigger**; `ci-macos-gate.yml` and `ci-macos-recheck.yml` have no push trigger
left to force past, so their `workflow_dispatch` is now the *only* way to run them at all (see
[macOS runs on request only](#macos-runs-on-request-only)):

```bash
gh workflow run verify.yml --ref <branch>
gh workflow run ci-macos-gate.yml --ref <branch>
gh workflow run ci-macos-recheck.yml --ref <branch>                  # cached
gh workflow run ci-macos-recheck.yml --ref <branch> -f no_cache=true # cold, no caches restored or saved
```

**Drift insurance.** A complete filter (or, for the two dispatch-only macOS workflows, a complete
input list) means the last green run matches the current inputs, but not the current world: runner
images, the Nix installer, Mathlib's olean cache, elan's and the Aeneas release's download servers
all move underneath an unchanged repository. One monthly schedule now covers that automatically:
`fresh-clone-canary.yml` replays the whole fresh-clone path, full gate included, on its two Linux
legs with no cache at all. The macOS side of that insurance is no longer automatic -- it is a
periodic request: dispatch `ci-macos-recheck.yml -f no_cache=true` for a cold macOS kernel replay,
and `fresh-clone-canary.yml -f macos=true` for a cold fresh-clone replay on both darwin
architectures (see "When to request a run" in [macOS runs on request
only](#macos-runs-on-request-only)).

**Verdict caching was considered and rejected.** Two further scale-back options were on the table:
skipping a whole recheck job when a cache entry keyed on its inputs records an earlier pass, and
the same per Comparator room. Neither is implemented. A restored verdict is a recorded claim
rather than fresh evidence, which undercuts the point of an *independent* recheck, and each adds
keying logic that must itself be kept exactly as complete as the path filters above, with a silent
false "pass" as the failure mode instead of a redundant run. Where Actions minutes are metered,
macOS minutes bill at 10x (see [macOS runs on request only](#macos-runs-on-request-only) and
[Cost](#cost) below); that multiplier sharpens the case for verdict caching but does not on its
own outweigh the loss of independent evidence above, so the rejection stands.

## macOS runs on request only

**The rule.** Every macOS job in this repository -- `ci-macos.yml`, `ci-macos-gate.yml`,
`ci-macos-recheck.yml`, and the two macOS legs of `fresh-clone-canary.yml` -- runs only when
requested (`workflow_dispatch`, or the canary's `macos` dispatch input), never automatically on a
push, a pull request, or a schedule. `intel-installer-smoke.yml` is the one documented exception:
it keeps a `pull_request` trigger, path-filtered to its own file, because it costs under two
runner-minutes per action bump and exists specifically to catch an installer-sunset regression on
the PR that introduces it (see that workflow's own header).

**The reason.** The macOS jobs are the slowest and most expensive in the repository, and the rule
dates from the tree's development in a private repository (commit `32265a3`, "ci: run every macOS
job on request only"). GitHub bills Actions minutes against the account's quota for a private
repository, with a per-OS multiplier -- macOS at 10x the Linux rate -- so a macOS job on every push
or on a monthly schedule cost real, billed minutes on every one of those triggers; making them
request-only put that cost under a maintainer's control instead of the repository's push traffic.
Standard hosted runners are free for a public repository, so the multiplier no longer binds here;
the automatic triggers have deliberately not been restored yet, and a private fork or mirror still
pays the metered rate. See [Cost](#cost) below for the figures and for what restoring would take.

**How to request each workflow** (append `--ref <branch>` to run it against a specific branch or
PR head rather than `main`):

```bash
gh workflow run ci-macos.yml --ref <branch>
gh workflow run ci-macos-gate.yml --ref <branch>
gh workflow run ci-macos-recheck.yml --ref <branch>                  # cached
gh workflow run ci-macos-recheck.yml --ref <branch> -f no_cache=true # cold, no caches restored or saved
gh workflow run intel-installer-smoke.yml --ref <branch>             # fallback; normally runs on its own PR
gh workflow run fresh-clone-canary.yml --ref <branch> -f macos=true  # adds the two macOS legs to the monthly Linux-only run
```

**What is not covered by default.** Without a request, no push or pull request evidences: the
aarch64-darwin build-and-test leg (`ci-macos.yml`'s `build` and `aeneas-prebuilt`), the aarch64-darwin
proof gate (`ci-macos-gate.yml`'s `aeneas-gate`), the macOS kernel replay
(`ci-macos-recheck.yml`'s `recheck-kernel`), the `launcher-compat` fixture's faithful run under
macOS's real `/bin/bash` 3.2 on either darwin architecture, and all of x86_64-darwin except one
thing: `ci.yml`'s `hygiene` job still evaluates both darwin dev shells on every push via
`nix flake check --all-systems`, so a broken x86_64-darwin shell definition is still caught without
a request. Everything x86_64-darwin actually *executes* -- `install.sh`, `check.sh
--committed-extraction`, the installer smoke (apart from its own PR trigger) -- requires a request.

**When to request a run.** Before a release (so the release commit itself is macOS-evidenced, not
just its ancestors); after a change to an input of the gate or the replay (anything
`ci-macos-gate.yml`'s or `ci-macos-recheck.yml`'s header lists, since neither runs automatically
to catch a regression there anymore); on a Dependabot bump that touches the Nix installer action
(`intel-installer-smoke.yml` normally catches this on its own PR trigger, but dispatch it directly
if that PR is skipped or the bump lands some other way); and after a long quiet period, as drift
insurance against a moving runner image, installer or download server (see [Drift
insurance](#trigger-policy) above -- the canary's monthly Linux-only schedule is now the only
automatic macOS-adjacent signal; requesting `-f macos=true` and `-f no_cache=true` periodically is
what replaces the two automatic monthly macOS schedules this repository used to run).

## Windows runs on request only

**The rule.** `ci-windows.yml` runs only when requested (`workflow_dispatch`), never automatically
on a push, a pull request, or a schedule -- the same rule as every macOS job above, stated here as
its own section rather than a silent extension of "macOS runs on request only", since this leg is
not macOS and the reason behind the rule differs (below).

**The reason.** Unlike the macOS rule, this is **not** a billing argument: this repository is
public, so standard hosted runners (including `windows-2025`) are free, with no per-OS multiplier
in effect. `ci-windows.yml` is dispatch-only because it is an exploratory, unproven leg that
validates a convenience install path (`docs/setup-without-nix.md`'s Windows section), not a claim
any certificate depends on, and because it is a fully cold run on every dispatch (no
`actions/cache`, see `ci-windows.yml`'s own header) -- so keeping it off the every-push path is
about runner time and the demo milestone's stated direction of fewer workflows running
automatically, not cost.

**How to request it**:

```bash
gh workflow run ci-windows.yml --ref <branch>
```

**Dispatch history.** Three dispatches so far, all this repository's own runs, evidenced on the
[Actions tab](https://github.com/benbrastmckie/SPSDemo/actions). The first died in both jobs at
"Install Nix inside WSL2" on an unrelated `curl` flag typo, fixed the same day. The second got
further: `wsl2-probe` was fully green (WSL2 + Nix provisioning, and Probes A-C all produced real
verdicts -- see [Known coverage gaps](#known-coverage-gaps) above), but `build` failed at
`lake build`, because `nix develop` itself could not realize a shell -- a CRLF-corrupted
`flake.nix` checkout, fixed by this repository's root `.gitattributes`. The third dispatch ran
against that fix and both jobs completed green: `wsl2-probe` finished in 7m17s (Probes A-D all
produced verdicts, including the recheck-prerequisites probe -- see [Known coverage
gaps](#known-coverage-gaps)), and `build` finished in 27m38s, with `lake build`, `cargo test`,
`check.sh --core-only` and all fourteen fixture-runner steps all passing. The WSL2 setup path is
validated end to end on `windows-2025` as of this run.

**What is not covered by default.** Without a request, no push or pull request evidences the WSL2
setup path at all: the flake's `x86_64-linux` build/test path is already covered on every push by
`ci.yml`'s `ubuntu-24.04` leg, but that leg says nothing about whether the WSL2 install procedure
itself works, or whether the recheck prerequisites (systemd, Landlock) are usable there -- both are
`ci-windows.yml`-only coverage, on request.

**When to request a run.** After a change to `docs/setup-without-nix.md`'s Windows section or to
anything `ci-windows.yml` mirrors from `build-and-test.yml` (see that file's "Keep in sync with
build-and-test.yml" marker); and periodically as drift insurance, the same rationale as the macOS
section's "When to request a run" above, since this leg has no monthly canary coverage of its own.

## ci.yml (CI badge)

Trigger: `push` and `pull_request` to `main`, plus `workflow_dispatch`. No `paths` filter; see
[Trigger policy](#trigger-policy).

Two jobs, run independently and in parallel: `build` (the Linux x86_64/aarch64 matrix, calling
[build-and-test.yml](#build-and-testyml-shared-job-body)) and `hygiene` (`ubuntu-24.04` only --
shellcheck, an `install.sh --help` smoke run, the launcher-compat fixture's static pass,
`check-spdx.sh` over the whole tree, `check-ci-docs-coherence.sh` (this page's own coherence
against `.github/`: every workflow inventoried, every `timeout-minutes:` and `paths:` entry
matching, every `uses:` SHA pin commented and single-valued, every anchor and cross-reference
resolving), `actionlint`, and `nix flake check --all-systems` over every dev shell including both
darwin systems). See the workflow file's own header comment for the full per-step breakdown and
why each check lives here rather than elsewhere.

Timeout: `hygiene` 15 minutes; `build` (via `build-and-test.yml`) 30 minutes.

Certifies: the flake's Linux build/test/lint path is green, and the repository's shell scripts and
workflow YAML are syntactically sound. Cache budget and per-push cost are in
[Cache strategy](#cache-strategy) and [Cost](#cost) below.

## ci-macos.yml (no badge)

Trigger: `workflow_dispatch` only -- on request (see [macOS runs on request
only](#macos-runs-on-request-only)). It is a separate workflow from `ci.yml` both so that the CI
badge and any required Linux checks never wait on macOS runner availability, and so that its
macOS jobs can be dispatched independently of the Linux ones.

Three jobs, a few minutes each: `launcher-compat` (both darwin architectures, no Nix -- the
`/bin/bash` 3.2 fixture that catches a bash-4-only construct in `full-gate.sh`/`install.sh`
before any Nix shell exists, and x86_64-darwin's only executed, not merely evaluated, check),
`build` (`macos-26`, calling [build-and-test.yml](#build-and-testyml-shared-job-body)), and
`aeneas-prebuilt` (`macos-26`, the only runtime check of `nix/aeneas-prebuilt.nix`'s darwin
re-sign path -- builds `.#packages.aarch64-darwin.charon-aeneas` and replays the extraction,
diffing against the committed files). See the workflow file's own header comment for the full
per-job mechanism (what each assertion checks and why) and
[docs/development.md](development.md#pin-bump-procedure) for the re-sign path's static
counterpart at pin-bump time.

Certifies: the macOS (aarch64-darwin) build-and-test leg is green, as of the last requested run.
`ci.yml`'s `hygiene` job additionally evaluates both darwin shells on every push via `nix flake
check --all-systems`, independently of whether this workflow has been requested.

## ci-macos-gate.yml and ci-macos-recheck.yml (no badge)

The two heavy macOS jobs, one per workflow file so that each gets GitHub's native `paths:` filter
over its own complete inputs (GitHub Actions has no per-job path filter). Both are `workflow_dispatch`-only
-- see [macOS runs on request only](#macos-runs-on-request-only) -- so today that `paths:` list no
longer gates a push or pull-request trigger; it still documents each job's complete input set, per
the maintenance rule in [Trigger policy](#trigger-policy), where the full lists live.

- `ci-macos-gate.yml` / `aeneas-gate`, on `macos-26`, 90-minute timeout: the real proof gate on
  aarch64-darwin, `bash full-gate.sh --yes` followed by a `certificate-freshness.sh
  --portable-host` step (the same assertion as `verify.yml`'s aarch64-linux leg). Deliberately no
  `--recheck`: darwin's recheck is partial by design and is the next job's. See the workflow
  file's own header comment for why it is driven through `full-gate.sh` rather than a hardcoded
  `.#extraction` reference.
- `ci-macos-recheck.yml` / `recheck-kernel`, on `macos-26`, 80-minute timeout. Runs
  `framed_channel/scripts/recheck-kernel.sh --bridge` and
  `framed_channel/scripts/recheck-comparator.sh --bridge` directly rather than the full gate,
  asserting every lean4lean/leanchecker/leanchecker-fresh line for core and bridge is `OK` and
  every Comparator line is `NOT-RUN`. This is the evidence for the "the kernel replay runs on
  macOS" portability claim (see
  [framed_channel/recheck/README.md](../framed_channel/recheck/README.md)); it uploads the
  verdict files as an artifact. See [docs/development.md](development.md#the-independent-recheck)
  for what the `no_cache` dispatch input does and the recheck's completeness story.

## build-and-test.yml (shared job body)

Not independently triggered or badged: this is the `workflow_call` job both `ci.yml` and
`ci-macos.yml` invoke per operating system, factored into one file so the two callers cannot
silently drift apart. Every leg runs the same steps, in order:

1. Checkout, then (on `ubuntu-24.04` only -- the step's `if:` compares the `os` input with that
   exact label, so it moves with the label; see [Runner images](#runner-images)) a disk-freeing
   step.
2. Install Nix (Determinate Nix installer).
3. The `lean-toolchain` composite action (restore, verify, self-heal and save `~/.elan`), then
   restore the `lake-core` cache (see [Cache strategy](#cache-strategy)).
4. `lake build` (`framed_channel/lean`), then `cargo test` (`framed_channel/rust`).
5. `check.sh --core-only`, asserting the process exits exactly 3 (INCOMPLETE by design; see
   [docs/development.md](development.md#the-fast-inner-loop-checksh---core-only----committed-extraction) for why this is
   not a failure).
6. The fixture test runners:
   `framed_channel/tests/{approvals,certificate-identity,adopt-recheck,ladder,spdx,ci-docs-coherence,aeneas-revs,recheck-revs,recheck-record,full-gate,bump-pin,lean-toolchain-pin,cert-freshness,landrun-shim}/run.sh`.
7. Save `lake-core` if it missed, only when the steps that populate it succeeded and the run was
   not cancelled.

Timeout: 30 minutes (sized for a cold macOS leg; see [Timeouts](#timeouts) below). Every step is
reproducible locally under `nix develop .#build`; see
[docs/development.md](development.md#the-fast-inner-loop-checksh---core-only----committed-extraction) for the fast-loop
commands this job's steps mirror.

## verify.yml (Verification badge)

Trigger: `push` and `pull_request` to `main`, filtered to the gate's inputs (see
[Trigger policy](#trigger-policy)), plus `workflow_dispatch`. A documentation-, fixture-
or other-workflow-only push runs `ci.yml` and `ci-macos.yml` alone.

Two jobs, each a `fail-fast: false` 2-leg matrix (x86_64-linux `ubuntu-24.04`, aarch64-linux
`ubuntu-24.04-arm`); every leg of both jobs runs on a push and bears the badge:

- `verify` (75-minute timeout) -- both legs run `bash full-gate.sh --yes` after a
  `full-gate.sh --support-level` step that fails the leg unless the system resolves `gate=full
  route=prebuilt`. A certificate-freshness step then fails the leg if the gate wrote anything
  different from what is committed (a strict `git diff --exit-code -- framed_channel/certificate`);
  the aarch64-linux leg's `--portable-host` variant blanks only the certificate's one
  host-dependent token (the target triple on `axioms.txt`'s `lean:` line), so a green aarch64-linux
  leg is evidence it reproduces the certificate byte-for-byte. See the workflow file's own header
  comment for the full step list and
  [docs/development.md](development.md#certificate-regeneration) for the regeneration command.
- `recheck` (90-minute timeout) -- both legs run `bash full-gate.sh --recheck --yes` for real
  inside the resolved `.#recheck` shell (comparator, the pinned landrun, charon/aeneas), hard-failing
  on a missing recheck prerequisite rather than silently degrading. The x86_64-linux leg is CI's
  producer of the canonical, complete recheck record, uploaded as the `recheck-record` artifact for
  any contributor to adopt with `framed_channel/scripts/adopt-recheck.sh`; a failing leg uploads a
  `recheck-diagnostics` artifact instead. See the workflow file's own header comment for the full
  step list (prerequisite checks, the producer-string bookkeeping, diagnostics collection) and
  [docs/development.md](development.md#the-independent-recheck) for running a genuine recheck
  locally.

Every job here that builds the bridge package shares the `mathlib-cache`, `substituter-probe` and
`lake-bridge` composite actions with the two macOS gate/recheck workflows and (for `lake-bridge`)
with `ci-macos.yml`; see [Cache strategy](#cache-strategy) for what each action does and its
budget.

Certifies: the committed certificate under `framed_channel/certificate/` matches what a fresh
gate run over the current tree produces, on both platforms, and the independent recheck of that
tree is complete and passes, on both platforms. The badge goes red whenever a recorded approval is
stale, by design. A narrow aarch64-linux package-level smoke build
(`.#packages.aarch64-linux.{lean-toolchain-bin,comparator}`, plus a `lean --version`/usage-output
check) is available as a local recipe for diagnosis on an aarch64 host, but is not itself a
workflow job: the `recheck` job's aarch64-linux leg already runs the complete aarch64-linux
recheck on every filtered push, which is the stronger and always-run coverage.

## Platform matrix

This table states current, mechanical occupancy: which system runs which job today, and what
evidence backs each row.

**The reproducibility claim, exactly**: the full gate reproduces from hash-locked inputs on
x86_64-linux, aarch64-linux and aarch64-darwin, and each of the three asserts a byte-identical
certificate in CI, per the new "Certificate freshness" column below (strict on x86_64-linux;
apart from the target triple, via `--portable-host`, on the other two -- see
[docs/development.md](development.md#certificate-regeneration)). The complete independent
recheck runs on Linux only. x86_64-darwin is a light audit, not a verification, under its
standing sunset decision (see [Known coverage gaps](#known-coverage-gaps)).

The four designated systems, by **support level** -- what `bash full-gate.sh --support-level`
(see `full-gate.sh --help`) resolves for that system, right now, at the current
`nix/aeneas-pin.json` pin. Every job in this table drives `full-gate.sh` itself (`verify.yml`'s
`verify` and `recheck` matrices, on both their x86_64-linux and aarch64-linux legs, and the
aarch64-darwin jobs `aeneas-gate`/`recheck-kernel`), so a future pin move that changes a row's
route changes what that leg actually does, not just what this table claims. `ci-macos.yml`'s
`aeneas-prebuilt` job is the one exception: it hardcodes `nix develop .#extraction` for its own
extraction refresh, independent of this table.

| OS | Support level | Gate command | Recheck | Certificate freshness | Workflow + job | Trigger |
|---|---|---|---|---|---|---|
| x86_64-linux | Full gate (`--aeneas` and `--recheck`), prebuilt route | `full-gate.sh --yes` / `full-gate.sh --recheck --yes` | complete | strict (byte-identical) | [verify.yml](#verifyyml-verification-badge) `verify` / `recheck` (x86_64-linux leg) | push/PR filtered to the gate's inputs, `workflow_dispatch` |
| aarch64-linux | Full gate (`--aeneas` and `--recheck`), prebuilt route -- **top priority** | `full-gate.sh --yes` / `full-gate.sh --recheck --yes` | complete | `--portable-host` (byte-identical apart from the target triple) | verify.yml `verify` / `recheck` (aarch64-linux leg) | same |
| aarch64-darwin | Full gate (`--aeneas`) when the pin carries a macOS asset; otherwise the fallback chain | `full-gate.sh --yes` | **partial by design** -- the kernel replay (Lean4Lean, leanchecker) runs for real; Comparator is `NOT-RUN` (Landlock's sandbox is Linux-only) | `--portable-host`, same as aarch64-linux | [ci-macos-gate.yml](#ci-macos-gateyml-and-ci-macos-recheckyml-no-badge) `aeneas-gate` / ci-macos-recheck.yml `recheck-kernel` / ci-macos.yml `build`, `aeneas-prebuilt`, `launcher-compat`; the canary's own `launcher-compat under /bin/bash (darwin)` step also covers this system, when requested | on request only (see [macOS runs on request only](#macos-runs-on-request-only)): `workflow_dispatch` for the gate, the recheck (with a `no_cache` input) and `ci-macos.yml`; `fresh-clone-canary.yml -f macos=true` for the canary leg |
| x86_64-darwin | Light shell only -- no upstream aeneas asset or from-source route on this platform | `check.sh --committed-extraction` | unavailable | N/A -- `check.sh --committed-extraction` writes nothing under `certificate/`; this is a light audit, not a verification | ci-macos.yml `launcher-compat` on `macos-15-intel` (`/bin/bash` 3.2, `gate=light-only` asserted, no Nix installed); intel-installer-smoke.yml `intel-installer-smoke` (the only Intel job that still runs automatically, on the pull-request path); no full-gate CI leg -- `ci.yml`'s `hygiene` job's `nix flake check --all-systems` still evaluates this system's dev shells on every push, independently of any request; the canary's `install.sh`, its own `launcher-compat under /bin/bash (darwin)` step, and `check.sh --committed-extraction` cover the rest, when requested | on request only: `ci-macos.yml` via `workflow_dispatch`; `fresh-clone-canary.yml -f macos=true`; `intel-installer-smoke.yml` PR-filtered to its own file (the documented exception), plus `workflow_dispatch` |

**The aarch64-darwin fallback chain**, in order, driven entirely by `full-gate.sh`'s own route
resolution (never re-implemented here): (1) the prebuilt route, when
`nix/aeneas-pin.json`'s `assets.aarch64-darwin` names an asset; (2) the consented from-source build
(`.#extraction-source`, ~30 min/~12 GiB, cost-prompted or `--yes`), when no prebuilt asset exists
and the pin does not record the from-source build as known-broken on this system; (3) the
`check.sh --committed-extraction` pre-check (`INCOMPLETE` by design, never certifying), when
neither of the above applies. `nix/aeneas-pin.json`'s top-level `macos_fallback` boolean is the
machine-readable signal that the pin bump's own middle-rule search took the Linux-complete branch
(rung 2/3 above is in effect); `bash full-gate.sh --support-level`'s `macos_fallback` key mirrors
the same field.

Linux x86_64 is where the committed certificate and the canonical, complete independent recheck
record are produced ([verify.yml](#verifyyml-verification-badge)).

**The non-Nix path** (`docs/setup-without-nix.md`) is not a fifth row of this matrix -- it is not
a Nix-driven gate at all, and stays out of scope for `full-gate.sh --support-level`. It is a
separately, narrowly covered path: [setup-without-nix.yml](../.github/workflows/setup-without-nix.yml)
exercises it with no Nix invocation of any kind, confirming only the elan/Rust install procedure
and `check.sh --committed-extraction` -- no full gate, no Charon/Aeneas install, no recheck.

**Windows is not a sixth row either**, and for a different reason than the non-Nix path above: it
is not a distinct platform at all. `docs/setup-without-nix.md`'s Windows section runs Nix inside a
WSL2 distribution, which the flake already treats as `x86_64-linux` (`flake.nix`'s `systems`
list) -- the same row this table already carries, already built by the `ubuntu-24.04` leg.
[ci-windows.yml](../.github/workflows/ci-windows.yml) validates the WSL2 *install path* (does the
documented procedure work, are the recheck prerequisites usable there), not a new platform; `bash
full-gate.sh --support-level` has no Windows-specific branch, and none is added by this leg. See
"Windows runs on request only" above and [Known coverage gaps](#known-coverage-gaps) below.

## Runner images

Every `runs-on:` names a concrete image -- `ubuntu-24.04`, `ubuntu-24.04-arm`, `macos-26`,
`macos-15-intel` -- never a floating `*-latest` label. GitHub re-points `ubuntu-latest` and
`macos-latest` at a new OS release on its own schedule, and this pipeline is sensitive to exactly
what changes then: the recheck depends on the runner kernel's Landlock ABI (landrun 0.1.17 asks
for ABI V9; the `ubuntu-24.04` kernel offers v7, which is why every landrun call here is
`--best-effort` with its guarantees probed), the launcher fixture depends on macOS still shipping
`/bin/bash` 3.2, and the darwin re-sign check depends on the image's codesigning behaviour. An
image move is therefore a reviewed change, made on purpose:

1. In one commit, replace the old label everywhere: `grep -rn 'ubuntu-24.04\b\|macos-26'
   .github/ docs/ framed_channel/ README.md`. `build-and-test.yml`'s disk-freeing step has an
   `if: inputs.os == '<label>'` that must move with it, or the step silently stops running; the
   canary's matrix and this page's tables carry the label too.
2. Push it on a branch and open a pull request. The workflow-file edits admit every filtered
   workflow, so the whole pipeline runs on the new image.
3. Read, in the `recheck` job's log, the `kernel Landlock ABI vN` line and the `[ok] landrun ...
   enforces Landlock` line; in `launcher-compat`, the `BASH_VERSION` line; in `aeneas-prebuilt`,
   the `installCheckPhase` output. Then merge.

The run log's "Set up job" group prints the image and its version; that is the record of what a
given run actually ran on.

## Cache strategy

Two kinds of Actions cache entry exist: `elan-*` (`~/.elan`) and `lake-*` (`.lake` build trees
and, for `lake-core`, the cargo target directory). No
workflow caches the Nix store and no workflow configures an extra substituter of any kind:
`cache.nixos.org` is the only substituter anywhere in this repository. Charon and aeneas come from
the pinned upstream Aeneas release's tarball (fixed-output downloads, verified by sha256; see
[docs/development.md](development.md#charonaeneas-provenance)) rather than a Nix-built,
cache-served derivation, so there is no charon/aeneas Nix-store cache to maintain at all.

Actions cache entries are immutable (a key, once saved, can never be overwritten) and a restore
is trusted blindly by everything after it. The policy below follows from those two facts.

**Before adding a new cache key, apply the consumption-pattern test.** Does this cache's content
get consumed by a build tool with its own staleness detection (Lake, Cargo), where an omitted
input just degrades to a slower build -- or does something execute an artifact from it directly
(an installed toolchain, a prebuilt tool binary, or any linked executable inside an otherwise
incremental tree), where an omitted input can leave a restored entry silently unrunnable? For the
second case the environment pin (here, the nixpkgs revision) is a required key input, however
incremental the surrounding tree looks; the elan and `lake-recheck` cases below are what that
omission actually costs. Two form rules follow from the same immutability fact and generalize
across every key family in this repository: an explicit epoch segment (see below), and no
`restore-keys` prefix fallback unless a wrong hit is provably no worse than a miss -- no key
family in this repository clears that bar today, so every key here is exact-key.

**`~/.elan` is owned by one composite action**, [`.github/actions/lean-toolchain`](../.github/actions/lean-toolchain/action.yml),
used by every job that runs `lake` (`build-and-test.yml`'s `build` job, `ci-macos-gate.yml`,
`ci-macos-recheck.yml`, and every leg of both `verify.yml` matrix jobs) -- the canary, both
`update-*` workflows and `setup-without-nix.yml` never call `lake`, so they never invoke this
action. It
needs the repository checked out and Nix installed first,
and it goes before anything that calls `lake` (in particular before a Mathlib cache retry loop). It:

1. computes the key `elan-v2-<os>-<arch>-<nixpkgs rev>-<hash of the three lean-toolchain files>`,
   where the nixpkgs rev is `flake.lock`'s root nixpkgs locked revision. On Linux nixpkgs' elan
   patches every toolchain it installs so that its ELF interpreter and `cc` wrapper are
   `/nix/store` paths of that revision; an entry made under another revision is dead on arrival.
   The rev rather than a hash of `flake.lock`, so a relock that moves only aeneas or rust-overlay
   does not re-save the entry. **A nixpkgs relock therefore invalidates the elan cache by design.**
2. restores on that exact key only -- no `restore-keys`. A prefix fallback is precisely what
   restores an entry made for different inputs; a miss costs one toolchain download.
3. on a miss (or `use-cache: false`), verifies the Lean release asset elan is about to fetch
   against `nix/lean-toolchain-pin.json`'s committed per-system sha256
   (`nix/lean-toolchain-pin.sh`) before the next step lets elan fetch it -- elan's own fetch has
   no hash verification of its own. A mismatch fails the job before anything is installed.
4. verifies: `lake --version` and `lean --version` inside the job's dev shell, in each of the three
   Lake packages ([verify.sh](../.github/actions/lean-toolchain/verify.sh), runnable by hand). On a
   miss this same call is what installs the toolchain. If the probe fails and self-heals (next
   step), the pin check above runs a second time before the reinstall, since that is also a fresh
   elan fetch.
5. self-heals once: on failure it emits a warning naming the cause, deletes
   `~/.elan/toolchains` and `~/.elan/update-hashes`, and probes again. A second failure is a hard
   error; one retry must never mask a genuinely broken toolchain pin.
6. saves, inside the action, immediately after a successful verification and only on a miss. At
   that point `~/.elan` is complete and nothing later in any job adds to it, so no cancelled or
   failed job can bank a partial tree, and no `always()` is involved.

Outputs (`cache-hit`, `verified`, `healed`, `saved`, `nixpkgs-rev`, `cache-primary-key`) appear in
every caller's step summary; a `pin-checked` output (`success`/`failure`/`skipped`) is also
available for a future caller's summary, though none reads it yet. `healed: true` on a run that
also reports `cache-hit: true` means
the cached entry itself is bad: bump the epoch. With `use-cache: false` (the macOS kernel replay's
uncached, `no_cache=true` dispatch) steps 2 and 5 are skipped: the verify step installs the
toolchains itself, exactly as on a miss, and the run leaves no entry behind.

**Every `lake`/`lean` call in a workflow runs from inside a Lake package directory.** elan picks
the toolchain from the working directory's `lean-toolchain` file; the repository root has none and
a runner's `~/.elan` has no default toolchain, so `lake --version` at the root fails with `no
default toolchain configured` however healthy the toolchain is. A developer machine with
`elan default` set hides this completely. To reproduce a runner's elan state locally, point
`ELAN_HOME` at a directory that has the installed toolchains but no default:

```bash
E="$(mktemp -d)"; ln -s ~/.elan/toolchains "$E/toolchains"
printf 'telemetry = false\nversion = "12"\n\n[overrides]\n' > "$E/settings.toml"
# fails: no lean-toolchain file at the root
ELAN_HOME="$E" nix develop .#build --command bash -c 'lake --version'
# works
ELAN_HOME="$E" nix develop .#build --command bash -c 'cd framed_channel/aeneas && lake --version'
```

**Every `.lake` cache is exact-key only, and saved only from a successful populate.** No `lake-*`
key has a `restore-keys` fallback: a `.lake` tree fetched for an older manifest contains an older
Aeneas checkout, and that stale checkout is how a correct pin was once reported as a charon-pin
mismatch. Each save's `if:` is `!cancelled()` plus the `outcome == 'success'` of the step that
populates the tree (`gate`, `recheck`, `recheck_kernel`, `build_recheck_tools`, or `lake_build` and
`cargo_test`), never `always()`: a later step's failure still banks a good build, while a failed
or cancelled
populate never banks a partial one. The cost is that the first run after a manifest bump is fully
cold for that tree; `lake exe cache get` still supplies Mathlib.

Two trees are coupled to the nixpkgs revision, not just `framed_channel/rust/target`:
`framed_channel/rust/target`'s test executables are linked by the dev shell's compiler wrapper
with a `/nix/store` glibc interpreter; it lives in `lake-core`, whose key carries the nixpkgs rev.
`lake-recheck`'s `lean4lean`/`lean4export` are coupled too, though less obviously: their ELF
*interpreter field* is the fixed literal `/lib64/ld-linux-x86-64.so.2` (re-measured with
`patchelf --print-interpreter`/`readelf -l` on x86_64-linux at nixpkgs
`6d663c0533ff269008fb84e45930151e37c99db9` -- unchanged from the prior measurement; re-measure
again if a toolchain bump changes how `leanc` links), which is what made this cache look
nixpkgs-independent. It is not: `nix-ld` resolves that literal path to a real `/nix/store` glibc
at run time -- at this pin, `/nix/store/<hash>-glibc-2.42-84/...` per the landrun sandbox
deviations `check.sh --recheck` records in `certificate/recheck.txt` -- and that resolved store
path moves with nixpkgs like any other closure member. A relock that drops the old glibc from the
runner's store, combined with a `lake-recheck` cache entry saved under the old nixpkgs revision,
is exactly what left the two recheck jobs unable to grant `landrun` an execute path for the
now-orphaned glibc: the restored `lean4lean`/`lean4export` binaries still declared the same
`/lib64/ld-linux-x86-64.so.2` interpreter, but `nix-ld` and `landrun`'s dependency scan resolve
that through the *runner's current* Nix store, which no longer had the old glibc. `lake-recheck`'s
key is therefore nixpkgs-rev-coupled the same way `lake-core`'s is, despite the interpreter string
itself never changing; see the epoch bump below (`lake-recheck-v3`).

`lake-bridge` is deliberately absent from this list. Its key (`lake-bridge-v3`) caches
`framed_channel/{lean,aeneas}/.lake`, and both packages' `lakefile.toml` declare only `[[lean_lib]]`
targets -- no `lean_exe`, no `extern_lib`, no `precompileModules` -- so the cached tree holds
`.olean`/`.ilean` only, with no linked executable for a nixpkgs revision to couple to. Its key is
therefore correctly exact-key (no `restore-keys`, per the immutability rule above) without a
nixpkgs-rev segment: this is the negative case of the consumption-pattern test above, not an
oversight.

**The epoch segment** (`v2` in `elan-v2-`, `lake-core-v2-`; `v3` in `lake-bridge-v3-`,
`lake-recheck-v3-`) is the only repository-side way to replace a bad entry, since keys are immutable: bump it in
[action.yml](../.github/actions/lean-toolchain/action.yml) for `elan`, or in the workflow's
`key:` for a `lake-*` entry, and every existing entry of that kind becomes unreachable at once
(and ages out after 7 unused days). Deleting an entry by hand (`gh cache delete <id>`) is budget
hygiene, never a correctness step.

**Cost of the `lake-recheck-v3` key**: every `nixpkgs`/`rust-overlay` relock now makes the
`lake-recheck` entry cold for the recheck jobs that use it, exactly like `lake-core` already was --
one extra `lake build lean4lean/lean4lean lean4export/lean4export` per architecture (a few
minutes) until the next entry is saved. Accepted deliberately: the entry is only about 125 MiB, and
a correct cold build is strictly better than a fast, silently-wrong cache hit pointing at an
orphaned glibc. On `verify.yml`'s `recheck` job (both legs run on every filtered push) that extra
build is a few Linux minutes, billed at 1x; on the macOS
`ci-macos-recheck.yml` / `recheck-kernel` job it is the same extra build billed at the 10x macOS
multiplier, but that job only runs when requested, so the cost lands on the maintainer's own
request rather than on every relock (see [Cost](#cost) above).

**The `lake-bridge` cache key's `path:` list is spelled out level by level, not a single directory
plus an exclusion**, because `actions/cache`'s glob resolution makes a naive exclusion a no-op
when a listed entry is an ancestor of it -- the mistake `lake-bridge-v2-*` made, archiving
Mathlib's 6.3 GiB build with everything else. See
[`.github/actions/lake-bridge/action.yml`](../.github/actions/lake-bridge/action.yml)'s header for
the full path list and the mechanism. The save step's "Cache Size" line (and the recheck jobs'
failure-diagnostics `du` breakdown) is the check that the exclusion is still taking effect: a
`lake-bridge` entry of more than about 1 GiB means it is not.

Closure sizes (`nix path-info -S[h]`, x86_64-linux, at the `nightly-2026.09.17-86158eb` pin --
re-measure after a future pin bump): the release tarball's own fixed-output download is 123.0 MiB;
`aeneas-prebuilt` (the patched, wrapped package) is 69.7 MiB on its own, 2.5 GiB including its
Rust-nightly closure; the offline MIR sysroot (`aeneas-mir-sysroot`) is 211.7 MiB. `lint` 0.7 GiB,
`build` 1.7 GiB (neither includes charon/aeneas/comparator/landrun at all -- see
[docs/development.md](development.md#running-the-full-gate-locally-opt-in)'s route table).
`extraction` adds the prebuilt figures above to `build`; `recheck` adds Comparator and landrun on
top of `extraction` (both built from source by this flake, no prebuilt route for either -- see
[docs/development.md](development.md#pinned-versions)), which is why it still needs the same
disk-freeing step `verify` uses (see `verify.yml`'s `recheck` job bullet above), though the total
is far below the pre-prebuilt-route closure this section used to describe.

Budget (10 GB per-repository cap; least-recently-used eviction above it; unused entries expire
after 7 days). Sizes are as measured with `gh cache list` during development. Re-measure the
steady-state total after a toolchain or manifest bump:

| Entry (key prefix) | Paths | Approx. size | Saved by |
|---|---|---|---|
| `elan-v2-*` (x86_64-linux) | `~/.elan` | 690 MiB | the `lean-toolchain` action, in whichever of `verify.yml`'s `verify`/`recheck` jobs or `ci.yml`'s `ubuntu-24.04` build leg verifies a miss first |
| `elan-v2-*` (aarch64-linux) | `~/.elan` | 690 MiB | the same action, in `verify.yml`'s `verify`/`recheck` (aarch64-linux leg) or `ci.yml`'s `ubuntu-24.04-arm` build leg -- `runner.arch` in the key keeps this entirely separate from the x86_64-linux entry |
| `lake-bridge-v3-*` (x86_64-linux) | `framed_channel/{lean,aeneas}/.lake`, minus Mathlib's own build directory (path list spelled out level by level, see above) | 752 MiB (the abandoned `v2` entry, which wrongly included Mathlib's build, was 2479 MiB) | either of `verify.yml`'s `verify`/`recheck` legs (x86_64-linux), when its gate/recheck step succeeded -- shared key, same concurrent-saver race as `elan-v2-*` |
| `lake-bridge-v3-*` (aarch64-linux) | same paths | 752 MiB | either of `verify.yml`'s `verify`/`recheck` legs (aarch64-linux), same condition |
| `lake-recheck-v3-*` (x86_64-linux, aarch64-linux) | `framed_channel/recheck/.lake` | about 125 MiB | `verify.yml`'s `recheck` job, either leg, when its recheck step succeeded |
| `lake-core-v2-*` (one per Linux/ARM/macOS leg) | `framed_channel/lean/.lake`, `framed_channel/rust/target` | 9-11 MiB each | `build-and-test.yml`, when `lake build` and `cargo test` succeeded |
| macOS `elan-v2-*`, `lake-bridge-v3-*`, `lake-recheck-v3-*` | as above | 670 MiB, 752 MiB, 125 MiB | the `lean-toolchain` action in whichever macOS job verifies a miss first; `ci-macos-gate.yml`'s `aeneas-gate` and `ci-macos-recheck.yml`'s `recheck-kernel` for the two `.lake` trees. Never by an uncached (`no_cache=true`) dispatch. Both are dispatch-only and can go more than 7 days between requested runs, so their `.lake` entries are often expired when they next run |

With Mathlib's build out of `lake-bridge`, steady state is the three `elan-v2-*` entries (about
2.0 GB), three `lake-bridge-v3-*` entries (about 2.2 GB), `lake-recheck`, `lake-core` and
the Nix installer's own entries (about 0.8 GB together): comfortably under the cap. A manifest
bump or nixpkgs relock leaves the superseded entries live for up to 7 days, during which usage can
approach the cap and least-recently-used eviction may cost a warm run.
`gh api repos/<owner>/<repo>/actions/cache/usage`
reports current usage; deleting superseded entries by id is safe (they are regenerable and, with
no prefix fallback, unreachable) and is the remedy if eviction starts costing warm runs. `elan-v2-*`
is shared across every job on the same `runner.os`/`runner.arch`; on a cold run the sharers race
to save it, and `actions/cache/save` logs "Unable to reserve cache" as a warning for the losers
rather than failing the job.

Mathlib's own build output is served by Mathlib's own cache rather than an Actions cache entry,
through one composite action, [`.github/actions/mathlib-cache`](../.github/actions/mathlib-cache/action.yml)
(`lake exe cache get` in `framed_channel/aeneas`, inside the dev shell its `shell:` input names;
[get.sh](../.github/actions/mathlib-cache/get.sh) is the step itself and is runnable by hand),
used by every job that builds the bridge (`ci-macos-gate.yml`, `ci-macos-recheck.yml`, and every
leg of both `verify.yml` matrix jobs; `build-and-test.yml`'s `build` job builds only the core
package, so it never calls this action) and always placed after the `lean-toolchain` action
has proved `lake` runs and after the job's `lake-bridge` restore: it is content-addressed, free, and
fetches thousands of files well under a minute for a revision Mathlib CI has already built,
whereas restoring the same content from the Actions cache would be slower and spend a third of
the 10 GB budget. When it misses (typically a manifest bump to a revision Mathlib CI has not yet
built), the action retries three times, then reports `outcome=miss` and the calling job compiles
Mathlib from source, which is correct and only slower, inside that job's timeout. The retry loop is for the network only: a
`lake` that cannot execute inside that loop is a hard job failure with its own message, not
attempt 2 of 3 (it used to be downgraded to a warning, which is how a dead toolchain once
surfaced much later as an unrelated-looking error).

Nothing the Verification badge certifies is read from an Actions cache: `check.sh --aeneas`
re-realizes the prebuilt Aeneas route (or a from-source build, on the opt-in fallback) and
re-extracts, and the certificate-freshness check compares the regenerated
`framed_channel/certificate/` against what is committed, independent of any Actions-cache
outcome. A cache miss makes a run slower, never incorrect.

## Cost

Standard hosted runners are free for a public repository. Where Actions minutes are metered (a
private repository, such as the one this tree was developed in, or a private fork), GitHub bills
them against the account's quota with a per-OS multiplier -- macOS runs at 10x the Linux rate and
Windows at 2x (Linux x86_64 and Linux arm64 both bill at 1x), current GitHub Actions billing policy
rather than something this repository measured; verify it against GitHub's own pricing page if it
matters to a decision. That multiplier is why every macOS job in this
repository was made on request only rather than running on every push or on a monthly schedule
(see [macOS runs on request only](#macos-runs-on-request-only)); `ci-windows.yml` is dispatch-only
for a different reason (runner time and exploratory status, not cost -- see "Windows runs on
request only" above), since the 2x Windows multiplier does not bind on this public repository
either. The figures below are wall-clock minutes per job, warm (exact-key
cache hits) unless marked cold, with the metered macOS cost (wall-clock x 10) alongside; per the
measured-figures convention above, each row's provenance and trigger follow the table rather than
being restated per cell:

| Job | Warm | Cold | Metered macOS cost (warm / cold) |
|---|---|---|---|
| `ci.yml` `hygiene` | about 2 | -- | N/A -- Linux only, 1x |
| `build-and-test.yml` leg (Linux x86_64, Linux arm64, macOS) | 4-5 | about 8 (macOS) | N/A for the Linux legs (1x); macOS leg: about 40-50 / about 80 |
| `ci-macos.yml` `aeneas-prebuilt` | about 3 | -- | about 30 / -- |
| `ci-macos.yml` `launcher-compat` | under 1 per architecture | -- | under 10 per architecture / -- |
| `verify.yml` `verify` (either leg) | about 5 | 17-20 | N/A -- Linux only, 1x |
| `verify.yml` `recheck` (either leg) | 17-24 (aarch64-linux leg about 18) | about 40 | N/A -- Linux only, 1x |
| `ci-macos-gate.yml` `aeneas-gate` | 7-9 | about 24 | about 70-90 / about 240 |
| `ci-macos-recheck.yml` `recheck-kernel` | about 37 | about 49 | about 370 / about 490 |
| `setup-without-nix.yml` | -- | 21-30 (no cache by design) | N/A -- Linux only, 1x |
| `ci-windows.yml` `wsl2-probe` | -- | about 7 (7m17s cold, this repository's own run, fully green, all four probes including the recheck-prerequisites probe) | N/A here (public repository, no metered cost); GitHub's own per-OS multiplier for Windows is 2x the Linux rate where minutes ARE metered, lower than macOS's 10x |
| `ci-windows.yml` `build` | -- | about 28 (27m38s cold, this repository's own run, a full green run; that figure predates the current, smaller command set and is now an upper bound) | N/A here; 2x where metered, same caveat as above |

**Provenance.** The `verify` and `recheck` (both legs each) warm figures and
`setup-without-nix.yml`'s cold figure are this repository's own runs; re-measure them before
lowering the matching [Timeouts](#timeouts) budget, or simply on reviewing that workflow's next
run. Every other figure in this table -- both cold columns for `verify`/`recheck`, every
`ci-macos*` row, `ci.yml` `hygiene` and `build-and-test.yml` -- is a development-repository
figure, carried as the best available estimate until this repository runs that job under those
conditions; the monthly canary (for the macOS `build-and-test.yml` leg) and the next uncached
`no_cache=true` dispatch (for `recheck-kernel`) are the occasions that would refresh them.
`ci-windows.yml`'s two figures are also this repository's own run, and both are genuine
full-job cold figures from its third dispatch (the first two dispatches did not reach a clean
build; see [Known coverage gaps](#known-coverage-gaps)): `wsl2-probe`'s 7m17s and `build`'s
27m38s, the latter measured against a larger command set than the job now runs.

An ordinary push (documentation, a fixture) runs `ci.yml` alone now: signal in about two
minutes, at 1x. A push that touches an input of the gate adds `verify.yml`; both run on Linux and
never bill at the macOS multiplier. The two `update-*` workflows and the canary's Linux legs are
schedule/dispatch-only, so none of them adds to a push either; see `update-aeneas-pin.yml`'s own
header for its profile (up to `--max-gates` sequential real gates in the worst case, still Linux,
still 1x).

Every macOS figure in the table above is incurred only when that workflow is explicitly requested.
The canary's two macOS legs, requested together with `-f macos=true`, add their own metered cost on
top of the Linux legs' 1x cost: the measured first-run wall-clock times were about 34 minutes
(aarch64-darwin) and about 57 minutes (x86_64-darwin) -- about 910 metered minutes combined (see
[Known coverage gaps](#known-coverage-gaps) for the run history those figures come from).

**What restoring the automatic macOS runs would take.** With standard hosted runners free for a
public repository, the per-OS multiplier no longer shapes anything here. The candidates to
restore: the `push`/`pull_request` triggers on `ci-macos.yml`, `ci-macos-gate.yml` and
`ci-macos-recheck.yml` (the last two already carry the `paths:` lists needed, documented but
currently inactive -- see [Trigger policy](#trigger-policy)); the monthly uncached `schedule`
removed from `ci-macos-recheck.yml`'s `on:` block (replaced by the `no_cache` dispatch input,
which itself can stay as a manual override); and `fresh-clone-canary.yml`'s `macos` matrix
selection defaulting to `true` so its monthly schedule again covers all four systems without a
dispatch. `intel-installer-smoke.yml`'s trigger needs no change either way, since it never depended
on repository visibility.

## Timeouts

| Job | Timeout | Sized for |
|---|---|---|
| `ci.yml` / `hygiene` | 15 minutes | Realizing the 0.7 GiB `lint` shell plus the checks, on the order of 2 minutes, with headroom for a slow substituter fetch. |
| `build-and-test.yml` (every caller) | 30 minutes | A cold leg on any of the three systems it runs (Linux x86_64, Linux ARM, macOS); a cold macOS run is the slowest of the three. |
| `verify.yml` / `verify` (either leg) | 75 minutes | The cold path: Lean caches miss but Mathlib's cache hits, or, slower still, Mathlib's cache also misses and `check.sh` compiles Mathlib from source. |
| `verify.yml` / `recheck` (either leg) | 90 minutes | The cold path: the same Lean-cache-miss/Mathlib-cache-miss cost `verify` is sized for, plus Comparator and landrun building from source on every cold `.#recheck` shell realization (charon/aeneas and lean-toolchain-bin are prebuilt fetches, not builds, at this pin). |
| `ci-macos-recheck.yml` / `recheck-kernel` | 80 minutes | The uncached (`no_cache=true`) dispatch is the sizing case: installing the toolchain, fetching and building the `recheck/` tools (lean4lean, lean4export) and the bridge's dependencies (Aeneas + Mathlib), then replaying every module of both packages twice (Lean4Lean and leanchecker); about 49 minutes with a cold bridge cache, a development-repository figure -- the next uncached `no_cache=true` dispatch on this repository re-measures it. |
| `ci-macos.yml` / `launcher-compat` | 5 minutes | No Nix and no build: one fixture under `/bin/bash`, well under a minute per architecture. |
| `ci-macos-gate.yml` / `aeneas-gate` | 90 minutes | Sized like `verify` (75 minutes) plus macOS cold-build headroom; also fits the consented from-source fallback (~30 min) should the pin ever lose its darwin asset. |
| `ci-macos.yml` / `aeneas-prebuilt` | 30 minutes | Realizing the prebuilt Aeneas route on `aarch64-darwin` (its `installCheckPhase`) plus one `refresh-extraction.sh` replay diffed against the committed files -- no Lean core/bridge build. |
| `setup-without-nix.yml` | 60 minutes | An uncached elan and Rust install plus `check.sh --committed-extraction`; 21-30 minutes on this repository's runs. |
| `ci-windows.yml` / `wsl2-probe` | 20 minutes | WSL2 provisioning, a from-scratch Nix install, and four short probes -- no build, no `full-gate.sh`. |
| `ci-windows.yml` / `build` | 60 minutes | Fully cold on every run by design (D2: no `actions/cache`, see the workflow's own header) -- WSL2 provisioning and a from-scratch Nix install, then `build-and-test.yml`'s full command set; `build-and-test.yml`'s own 30-minute cold-macOS sizing plus headroom for the extra provisioning/install cost this leg alone pays. |
| `fresh-clone-canary.yml` | 120 / 120 / 105 / 120 minutes (x86_64-linux, aarch64-linux, aarch64-darwin, x86_64-darwin) | Every leg fully cold by design. The x86_64-darwin leg is light-only, but that names the gate, not the cost: `check.sh` still runs the cold bridge-package build (27.3 silent minutes on aarch64-darwin, 48.6 on Intel) on a slower runner, so it is sized like the Linux legs. The first completed run measured 40m07s / 28m50s / 33m58s / 56m52s against those four budgets. |
| `intel-installer-smoke.yml` / `intel-installer-smoke` | 15 minutes | Checkout plus one `nix-installer-action` install and a `nix eval`; the installer step measured 1.3 minutes on the canary's Intel leg. No build and no gate -- see that workflow's header for why only the installer is under test. |
| `update-flake-inputs.yml` | 90 minutes | One relock, `nix flake check --all-systems` and one real `full-gate.sh --yes` on a closure nothing has cached yet. |
| `update-aeneas-pin.yml` | 180 minutes | Sized for the worst case: up to `--max-gates` (4) sequential real gates (each comparable to `verify`'s own cold-path cost) during an in-window search that fails several candidates before succeeding. A timeout here means no PR that week, not an incorrect one; the weekly schedule retries. Schedule plus `workflow_dispatch`. |

## Repository settings

One-time settings this pipeline depends on. None is stored in the repository, so a fork, a
transfer or a fresh publication has to set them again:

- **Settings -> Actions -> General -> Workflow permissions -> "Allow GitHub Actions to create and
  approve pull requests"**: on. `update-aeneas-pin.yml` and `update-flake-inputs.yml` open their
  proposals with the repository's own `GITHUB_TOKEN`; without this their last step fails with a
  permissions error. The default token permission can and should stay **read**: every workflow
  declares its own `permissions:` block.
- **Labels `dependencies` and `github-actions`**: Dependabot applies both
  (`.github/dependabot.yml`) and does not create custom labels itself.
- **Branch protection on `main`** (recommended, not required by any workflow): require the `CI`
  checks. Do not require a path-filtered workflow's checks: GitHub leaves a required check
  "pending" forever on a pull request whose paths do not admit the workflow.

**Workflow security posture**, which a change to any workflow must preserve:

- Every workflow declares top-level `permissions: contents: read`. Only the two `update-*`
  workflows widen it (`contents: write`, `pull-requests: write`), and neither runs on `push`,
  `pull_request` or any event a fork can cause -- schedule and `workflow_dispatch` only.
- Every `actions/checkout` step sets `persist-credentials: false`, so no job's local git config
  carries an ambient push credential after checkout. The two `update-*` workflows, which do write
  to the remote, pass their own `token: ${{ secrets.GITHUB_TOKEN }}` to
  `peter-evans/create-pull-request`, which configures its own push credential rather than relying
  on the checkout's.
- No workflow uses `pull_request_target` or `workflow_run`, so no workflow ever runs a fork's code
  with this repository's write token or secrets. A fork's pull request runs the `pull_request`
  workflows with a read-only token.
- No repository secret exists or is needed. `update-aeneas-pin.yml` passes `github.token` as
  `GH_TOKEN` to one step, because `gh api` refuses to run in Actions without a token; every read
  it makes is of a public repository.
- Every third-party action is pinned by full commit SHA with its version in a trailing comment;
  Dependabot moves SHA and comment together, weekly, in one grouped pull request that covers the
  workflows and the composite actions alike.
- No `${{ }}` expression that a contributor controls (branch name, PR title, dispatch input) is
  interpolated into a `run:` script; a dispatch input reaches a script only through `env:`.

## Known coverage gaps

- There is no `.shellcheckrc` in this repository. `ci.yml`'s `hygiene` job runs shellcheck with
  `-x -S warning`: sourced helper scripts are followed, and warnings and errors fail the job,
  while the tracked scripts' info- and style-level findings (about thirty, all deliberate) do not.
- **The push/pull_request-filtered workflows are only as complete as their `paths:` lists.**
  `verify.yml` and `setup-without-nix.yml` keep a genuine, active filter: a regression caused by a
  file outside their lists would surface only at the next admitted push or a manual dispatch.
  [Trigger policy](#trigger-policy) states the audit behind each list and the rule for extending
  it. `ci-macos-gate.yml` and `ci-macos-recheck.yml` carry the same kind of input list, but it no
  longer gates an active trigger -- see the next bullet.
- **The macOS workflows are dispatch-only, full stop.** `ci-macos.yml`, `ci-macos-gate.yml` and
  `ci-macos-recheck.yml` run only on `workflow_dispatch`; none of the three has any push, pull
  request or schedule trigger left (see [macOS runs on request
  only](#macos-runs-on-request-only)). A regression in any of them, caused by any file, surfaces
  only when a maintainer explicitly requests that workflow -- there is no residual "filtered but
  still automatic" middle ground the way there is for `verify.yml`. `fresh-clone-canary.yml`
  remains genuinely schedule-plus-dispatch, but only for its two Linux legs by default; its two
  macOS legs join only via the `macos` dispatch input.
- **Dispatch- and schedule-only workflows, first-run status.** The dispatch- and schedule-only
  workflows have now been exercised by `workflow_dispatch` against a hardened `main`, per this
  page's own no-stale-IDs convention (see the top of this page) -- see the Actions tab for the
  current run. `fresh-clone-canary.yml` took three dispatches to reach green: the first was
  cancelled at its original 45-minute `x86_64-darwin` budget during a cold bridge-package build
  (a mis-sized budget, not a repository defect); the second failed on `x86_64-darwin` inside an
  `install.sh` warm-up step that fetched from a third-party CDN -- a genuine repository defect (a
  flaky download for something outside the verification path should never fail a fresh clone),
  fixed by dropping that warm-up; the third was green. `fresh-clone-canary.yml`'s `x86_64-linux`, `aarch64-linux` and
  `aarch64-darwin` legs passed cleanly, including `install.sh` under macOS's `/bin/bash` 3.2 on
  `aarch64-darwin` (`launcher-compat` alone exercises `install.sh --help` and `full-gate.sh`, not
  a full install -- the canary's `bash install.sh` step is the actual full-install evidence). At
  120 minutes (see the Timeouts table) and with the warm-up fix, the `x86_64-darwin` leg has
  since completed green in 56m52s, so a fresh clone reproducing on `x86_64-darwin` is **no
  longer unproven** -- within the limit of what that leg runs: `install.sh` and
  `check.sh --committed-extraction` only, with `full-gate.sh` and the substituter probe skipped
  by design (`gate=light-only`). The full gate remains unevidenced on this platform, which is
  the standing gap, not the budget. That leg's log also reports that the Determinate Nix
  installer no longer supports Intel macOS and is falling back to a pinned last-supporting
  release, so this leg rests on an installer path that is no longer maintained upstream.
- **x86_64-darwin installer sunset.** The fallback named just above is upstream's, not this
  repository's: `nix-installer-action` emits an `::error::` on Intel macOS and then pins *itself*
  to the last Intel-supporting installer release, in its own words "a temporary fallback". The
  annotation cannot be suppressed (the action logs it before it reads `source-tag`) and does not
  fail the step. This repository deliberately passes **no** `source-tag`: doing so would add the
  only version pin in the tree that no automation owns -- invisible to Dependabot, whose
  `github-actions` ecosystem moves `uses:` SHAs and not action inputs (see
  [development.md](development.md)'s per-dependency-class table) -- in order to prolong a platform
  upstream has already dropped. `intel-installer-smoke.yml` instead detects the transition on the
  Dependabot PR that causes it. **Standing decision: when that fallback is removed upstream, the
  Intel legs are retired rather than pinned to a dead installer release.**
- `update-flake-inputs.yml` passed and exercised its PR-opening path on its first run.
  `update-aeneas-pin.yml` took two dispatches: the first exposed and fixed a repository defect (a
  trailing-newline bug in `nix/bump-aeneas-pin.sh`'s `restore_touched` that could spuriously flip
  its `changed` output); a defense-in-depth JSON-extraction fix was also applied to the PR-body
  step for the second. A schedule- or dispatch-only workflow's run listed in
  the Actions tab remains the durable evidence; after publishing, forking or transferring
  this repository, dispatch each once (`gh workflow run <file>`) rather than waiting for the
  schedule to find a problem.
- **Two rules the Linux recheck depends on, each learned from a failure no development host
  reproduces.** (1) A development host's Landlock ABI says nothing about a runner's: anything
  that invokes landrun without `--best-effort` works on a recent kernel and fails on every hosted
  runner, so every landrun call is `--best-effort`, with what best-effort could silently drop
  probed instead of assumed (a write under `--ro /` must be denied, and a TCP connect with no
  grant must fail with EACCES). (2) A Comparator room must see what the tree that built its linked
  packages saw -- the same `lake` binary (nixpkgs' elan wraps `lake` in a bash script the sandbox
  cannot execute, so the rooms resolve `lake` to the wrapped binary, recorded in `recheck.txt` as
  a `PATH: lake is ...` line) and every environment variable a lakefile of the workspace reads
  (today exactly one, `CI`, handed down through `systemd-run`, the outer landrun and the shim and
  recorded as an `--env CI=...` deviation line; `grep -n getEnv` over the lakefiles under
  `framed_channel/aeneas/.lake/packages` after a Mathlib or Aeneas bump). To run the rooms exactly
  as a runner does, see [docs/development.md](development.md#troubleshooting), "Comparator passes
  locally and fails on a runner".
- The Actions cache's 10 GB per-repository ceiling (with least-recently-used eviction) is a hard
  cap this repository operates under; see [Cache strategy](#cache-strategy) above for the current
  budget against it.
- **The WSL2 install path has been dispatched three times and is now fully validated, with real
  remaining caveats.** `ci-windows.yml` exists (dispatch-only; see "Windows runs on request only"
  above); its third dispatch is this repository's own run, evidenced on the [Actions
  tab](https://github.com/benbrastmckie/SPSDemo/actions), and both jobs finished green. The first
  dispatch died in both jobs on an unrelated `curl` flag typo; the second reached `nix develop`
  and failed there -- this repository carried no root `.gitattributes`, so the Windows runner's
  `core.autocrlf=true` checked `flake.nix` out with CRLF line endings, corrupting the shell script
  a derivation then embedded literally inside the file, killing `nix develop` (and everything
  depending on it: Probe C, Probe D, `lake build`) identically everywhere it was invoked. Fixed
  with a root `.gitattributes` (`* text=auto eol=lf`; see that file's own header for the full
  diagnosis and why a redundant per-workflow `core.autocrlf` step was not also added). The third
  dispatch, against that fix, is the evidence: `wsl2-probe` (7m17s) produced real verdicts for all
  four probes, and `build` (27m38s) ran `lake build`, `cargo test`, `check.sh --core-only` and all
  fourteen fixture-runner steps to completion, all green. Probe D's verdict:
  the recheck prerequisites are usable under WSL2 on this runner without a linger step --
  `recheck_systemd_user_usable`, `recheck_landlock_enforced` and `recheck_landlock_abi` (ABI v7)
  all report the same result with and without `loginctl enable-linger`, so linger makes no
  difference here. **What remains genuinely open, not resolved by this run**: `$GITHUB_OUTPUT`,
  `$GITHUB_ENV`, `$GITHUB_STEP_SUMMARY` and `$GITHUB_WORKSPACE` are still not reachable from
  inside the WSL2 shell (Probe A, confirmed on both the second and third dispatch), so any step
  needing them must go through the host shell instead, as `ci-windows.yml`'s own step-summary
  fallback does; the checkout mounts as `v9fs`, not DrvFs or ext4; the CRLF fix via the root
  `.gitattributes` is load-bearing for `nix` to work at all on a Windows checkout, not an
  incidental cleanup; and the leg stays `workflow_dispatch`-only and cold on every run (D2: no
  `actions/cache`), at about 28 minutes as measured on that dispatch -- an upper bound now, since
  the job's command set has since shrunk. See the [Platform matrix](#platform-matrix) above
  and `docs/setup-without-nix.md`'s Windows section for the full evidence trail.
- **`ci-windows.yml` mirrors `build-and-test.yml`'s command set by hand, not by calling it** (the
  architecture decision recorded in `ci-windows.yml`'s own header): the two files can drift, and
  drift here would be silent, since `ci-windows.yml` is dispatch-only (see "Windows runs on
  request only" above) -- a step added to `build-and-test.yml` without a matching addition to
  `ci-windows.yml` surfaces only at the next requested Windows run, if anyone notices the mirror
  is now incomplete. Accepted for this leg specifically because it validates a convenience install
  path rather than a claim any certificate depends on (see the workflow header's D1 rationale); a
  mechanical drift-check fixture asserting the two files' step lists agree is a named follow-up,
  not implemented here.
- `update-aeneas-pin.yml`'s and `update-flake-inputs.yml`'s pull requests are opened with the
  default `GITHUB_TOKEN`, which does not start this repository's other pull_request workflows
  on its own (a GitHub Actions restriction, not a bug here): their runs are created but held
  at "Action required" until a maintainer approves them, as observed on
  `update-flake-inputs.yml`'s first PR. The in-job gate is the only automated confirmation
  such a PR carries until a maintainer approves those held runs from the PR's checks list or
  the Actions tab, per the PR body's checklist.
- **Whether the two bot workflows commit the regenerated certificate themselves**:
  `update-flake-inputs.yml` does -- its `add-paths` includes
  `framed_channel/certificate/{axioms,countermodels,digests,ladder}.txt` alongside `flake.lock`.
  This is safe because its in-job `bash full-gate.sh --yes` step already runs on `ubuntu-24.04`
  (x86_64-linux), the exact architecture whose certificate `certificate-freshness.sh` commits, and
  that step already rewrites the four files in the runner's tree before the PR is opened -- they
  were previously just excluded from `add-paths`. Its maintainer checklist was updated to drop the
  now-redundant "regenerate" item and keep only "re-approve any stale item", the one judgment call
  that remains a human's. `update-aeneas-pin.yml` does **not** get the same treatment, deliberately:
  `nix/bump-aeneas-pin.sh`'s search loop can visit and gate several candidates, restoring
  `nix/aeneas-pin.json`/`flake.lock`/`framed_channel/aeneas/{lakefile.toml,lake-manifest.json}` to
  the pre-search state on a candidate's gate failure (`restore_touched`), but that restore list
  never includes the certificate files -- they are left exactly as the last real `check.sh` run
  (pass or fail) wrote them. Because the script's final "apply the winner" step re-applies the
  selected candidate's pin without re-running the gate, a run that tries and rejects a later
  candidate after its actual winner already passed leaves the certificate describing that
  *rejected* candidate, not the one actually pinned. This only happens on the `linux-complete`
  (`macos_fallback: true`) branch when at least one "C" candidate was visited and failed, but the
  workflow cannot know in advance whether that will occur, so the correspondence this would need
  does not reliably hold; `update-aeneas-pin.yml`'s `add-paths` is left unchanged and its
  maintainer checklist keeps the "regenerate the certificate" item. The practical consequence for
  a maintainer differs by workflow: once its held runs are approved, an `update-aeneas-pin.yml` PR
  is still expected to fail `verify.yml`'s certificate-freshness step, because `nix/aeneas-pin.json`
  is a certified input whose hash the certificate records and the bot moves it without regenerating
  -- that PR is never mergeable on green checks alone. An `update-flake-inputs.yml` PR now arrives
  with that certificate already regenerated, so only the human re-approval is outstanding.
- `setup-without-nix.yml` confirms the pinned Aeneas release asset still resolves upstream with an
  HTTP HEAD only (no download), independently of the Nix-driven jobs' own substituter probes; a
  deleted release or a renamed asset would be caught here even though this leg never installs Nix.
- `ci-macos-recheck.yml`'s uncached dispatch mode (`-f no_cache=true`, `USE_CACHE=false`, no
  Actions cache restored or saved) has not yet run in this repository; the cached dispatch mode
  has. There is no longer a "filtered" mode for this workflow at all -- only cached-dispatch and
  uncached-dispatch, both requested by hand.
- `update-aeneas-pin.yml`'s `workflow_dispatch` carries a `tag` input (report-only: forces
  `nix/bump-aeneas-pin.sh --tag <value>` instead of the automatic search; the result is still
  never applied without a normal PR review) that has not yet been exercised here.
- **A second, independent x86_64-darwin retirement trigger.** Beyond the installer-fallback
  removal named above, `flake.nix` documents nixpkgs 26.05 as the last release supporting
  x86_64-darwin at all; when nixpkgs moves past that release, the system and its
  CI leg are dropped together, regardless of whether the Nix installer fallback is still available.
  Either trigger firing retires the system the same way.

## Navigation

- [docs/README.md](README.md)
- [Back to README](../README.md)
