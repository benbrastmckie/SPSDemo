# Development loop

This page walks a contributor through the loop from a clean checkout to a committed certificate,
in the order the loop is actually run. Every command shown is copy-pasteable; flag lists and exit
codes are each script's own `--help`/usage text, linked rather than repeated here.

Start with `nix develop` from the repository root -- the **light shell**, which supplies only the
lint and build toolchains (Rust, elan, jq, perl and git). It never realizes charon,
aeneas, comparator or landrun, so entering it never costs a build, a fetch, or an account/token of
any kind; see [installation.md](installation.md) for the full
environment description and every dev-shell name (`default`, `full`, `extraction`,
`extraction-source`, `recheck`, `lint`, `build`).

## The fast inner loop: check.sh --core-only / --committed-extraction

```bash
bash framed_channel/check.sh --core-only            # offline pre-check; no extraction needed at all
bash framed_channel/check.sh --committed-extraction # audits both packages against the committed
                                                     # extraction, still without charon/aeneas
```

`--core-only` is offline, no network, no charon/aeneas bridge, and writes nothing under
`framed_channel/certificate/`. `--committed-extraction` goes one step further: inside the same
light shell, it builds and checks both packages (the core and bridge package, six certified units
between them) against whatever is already committed at
`framed_channel/aeneas/FramedChannelAeneas/Extracted/`, without ever regenerating or verifying
that extraction (no charon/aeneas needed for that either -- only `jq`). Both always end INCOMPLETE
(exit code 3) -- this is the expected outcome by design, never a failure, and neither one can be
mistaken for the verification claim: `--committed-extraction`'s own staleness stage prints
`[skip] ... NOT CHECKED` rather than silently passing. Run one of these after every edit; they are
the fast pre-checks for the stages that do not need to regenerate the extraction (build, format,
lint, license headers, and -- for `--committed-extraction` -- the proof stages themselves). See
`bash framed_channel/check.sh --help` for the full stage list and every flag.

**The two are NOT interchangeable for one specific defect class.** `--core-only` is the only mode
that leaves the bridge package out entirely (`bridge_ran=false`, `ran_packages=(core)`);
`--committed-extraction` still builds and audits the bridge package (`bridge_ran=true`), just
without regenerating or re-verifying the extraction it is built against. That difference matters
because `owner_of_proof`/`owner_of_supporting`'s bridge-vs-core classification and
`check_record`'s `unaudited` exemption (see `check.sh`'s manifest cross-check stage) are reached
in every mode, but their bridge-absent branch -- the one a bridge-owned name's classification
defect can hide in -- fires only when `ran_packages` does not include `bridge`, i.e. only under
`--core-only`. A defect confined to that branch passes both `--committed-extraction` and the full
gate locally and is caught only where something actually runs `--core-only`: see the pre-push hook
below, and every CI build leg. Run `--core-only` at least once before relying on
`--committed-extraction` alone for a change that touches ownership classification, the manifest,
or `check_record`.

## Pre-push hook: `check.sh --core-only` before every push

`install.sh` (the step every contributor already runs -- see [installation.md](installation.md))
activates a tracked git hook, `.githooks/pre-push`, via `git config core.hooksPath .githooks`. It
runs `check.sh --core-only` before every `git push` and treats the pre-check's own by-design
INCOMPLETE (exit 3) as the pass condition; any other exit -- including an unexpected 0, which
would mean `check.sh` claimed PASS without the bridge -- aborts the push. This closes exactly the
coverage gap the previous paragraph describes: `full-gate.sh` never runs `--core-only` (see its
own header), so without this hook a `--core-only`-only defect was invisible until a CI build leg
caught it after the push.

For a deliberate work-in-progress push, skip the hook once with `SKIP_CORE_ONLY_HOOK=1 git push
...`. Prefer this over `git push --no-verify`, which would also skip every other hook this
repository ever adds. If `core.hooksPath` is already set to something else in your checkout,
`install.sh` leaves it alone and prints the exact command to opt in manually
(`git config core.hooksPath .githooks`); see `.githooks/pre-push`'s own header for the hook's
full contract, including its `nix`-resolution fallback.

## Running the full gate locally (opt-in)

```bash
bash full-gate.sh --dry-run   # report the resolved route and its real cost; builds/fetches/asks nothing
bash full-gate.sh             # the real gate ([y/N] prompts for any demanding step)
bash full-gate.sh --yes       # same, non-interactive
bash full-gate.sh --recheck --yes
```

`full-gate.sh` (repository root) is the one opt-in entry point for the real verification claim. It
resolves the fastest available route for your system from `nix/aeneas-pin.json`:

1. **Prebuilt** (`.#extraction`, or `.#recheck` under `--recheck`) when the pin has a release
   asset for your system -- currently all three supported systems (x86_64-linux, aarch64-linux,
   aarch64-darwin). Seconds: a ~130 MB release tarball and ~290 MiB of Rust nightly downloads,
   both fixed-output downloads from `cache.nixos.org` and
   `static.rust-lang.org`, plus a ~112 MB MIR sysroot built locally offline from the pinned Rust
   nightly's vendored sources -- no charon/aeneas source build, no account, no token.
2. Otherwise, a from-source build (`.#extraction-source`) after an explicit
   cost prompt (~30 min, ~12 GiB) -- skipped automatically, straight to step 3, when the pin
   records that system's from-source build as known-broken. This auto-skip and the decline
   fallback to step 3 below both apply only to this implicit route.
3. Otherwise (or on declining step 2's implicit prompt), `check.sh --committed-extraction` in the light `.#build`
   shell: the audit above, printing `INCOMPLETE` and never certifying.

Passing `--source` explicitly forces an attempt at step 2 regardless of a known-broken record
(only appending a warning to the cost prompt) and, if declined, exits 0 with nothing to fall back
to -- it never drops to step 3, since asking for `--source` was itself an explicit choice.

`x86_64-darwin` always takes step 3 (its nixpkgs has dropped the aeneas flake's platform, so no
from-source route exists there either). Every demanding step (a from-source build, the ~7 GB
bridge fetch, a from-source Comparator/landrun build under `--recheck`) is `[y/N]`-prompted;
`--yes` accepts all of them non-interactively, and a non-interactive session without `--yes` exits
2 rather than silently choosing. `--dry-run` prints the resolved route and its real cost and exits
0 without building, fetching or asking anything -- run it first. `--recheck` needs the prebuilt
route (`.#recheck` already bundles Comparator/landrun alongside charon/aeneas); a `--recheck`
request that resolves to the source-fallback or committed-extraction route is dropped with a
printed note, since no shell combines the from-source aeneas route with Comparator/landrun. See
`bash full-gate.sh --help` for the full flag list, and `bash framed_channel/check.sh --help` for
every `check.sh` flag it passes through (`--clean`, `--lean-only`, `--require-person-approval`,
and more).

An exit code 0 from a real gate run of `full-gate.sh` (or an equivalent direct `nix develop .#extraction --command
bash framed_channel/check.sh --aeneas`, if you already know your system's pin has a prebuilt
asset) is the verification claim. `--dry-run` and `--support-level` also exit 0 without running
the gate at all (they only resolve and report a route), and declining an offered `--source`
fallback with no prebuilt asset also exits 0 while falling back to the `--committed-extraction`
pre-check -- none of these three is the verification claim.

## The refresh scripts

Each of these regenerates one committed artifact and is run only when its own trigger applies;
each links its own header comment for the exact usage and requirements rather than repeating them
here.

- [refresh-extraction.sh](../framed_channel/scripts/refresh-extraction.sh) -- after any
  `rust/src` edit, regenerates the Charon/Aeneas extraction.
- [refresh-vectors.sh](../framed_channel/scripts/refresh-vectors.sh) -- after regenerating the
  extraction, regenerates the differential vectors that Rust tests compare against.
- [refresh-hashes.sh](../framed_channel/scripts/refresh-hashes.sh) -- after deliberately changing
  a registered statement or bumping the toolchain, regenerates the statement-hash column of every
  registry (core registry first; the bridge registry imports it).
- [refresh-candidates.sh](../framed_channel/scripts/refresh-candidates.sh) -- regenerates the
  Select candidate set from the pinned Charon LLBC.

## Approvals

```bash
bash framed_channel/approve.sh --review --aeneas
# edit the review file, mark items "yes"
bash framed_channel/approve.sh --record FILE --approver "Name <email>" --aeneas
```

`--review` writes a review file with every item defaulted to "no"; a person (or an agent assisting
them) edits it and marks items "yes". `--record` re-computes every digest, refuses if anything
changed since the review, and writes the approved records. See
[certificate/README.md's Select, Specify and approval section](../framed_channel/certificate/README.md#select-specify-and-approval)
for the approval-unit and digest rules, and `bash framed_channel/approve.sh --help` (a real flag,
printing its own header) for the full flag list.

## Certificate regeneration

```bash
bash full-gate.sh --yes
bash framed_channel/scripts/certificate-freshness.sh                   # x86_64-linux: strict
bash framed_channel/scripts/certificate-freshness.sh --portable-host   # any other host
```

Run the full gate (`full-gate.sh`, or the direct `nix develop .#extraction --command bash
framed_channel/check.sh --aeneas` when your system's pin has a prebuilt asset), then confirm
nothing under `framed_channel/certificate/` changed; if it did, commit the regenerated files. This
is exactly what [verify.yml](ci.md#verifyyml-verification-badge)'s "Certificate freshness" step
checks in CI -- editing `flake.nix`, `nix/aeneas-pin.json` or any other digested certificate input
without regenerating and committing the certificate is what turns that step red.

The committed certificate is the one the x86_64-linux gate writes, because `verify`'s x86_64-linux
leg compares byte-for-byte. Exactly one token of it depends on the host: the
target triple on `axioms.txt`'s `lean:` line, which is `lean --version` verbatim. On aarch64-linux
or macOS a gate run therefore always rewrites that line; `--portable-host` ignores that one token
and nothing else, and is what `verify`'s aarch64-linux leg runs. Do not commit an `axioms.txt`
regenerated on another host when that line is its only change (restore it with `git checkout --
framed_channel/certificate/axioms.txt`). When a digested input really changed, regenerate on
x86_64-linux. From another host the regenerated files are the same ones once that line carries the
committed triple again -- a green aarch64-linux leg is the standing evidence that nothing else
differs -- and the x86_64-linux leg confirms it byte-for-byte on the push.

## The independent recheck

```bash
bash full-gate.sh --recheck --yes
```

The kernel replay (Lean4Lean, leanchecker) runs on any platform with the pinned Lean toolchain;
Comparator needs Linux's Landlock sandbox and is reported `NOT-RUN` everywhere else, so a local
`--recheck` on macOS (or a Linux host missing `landrun`/`systemd-run --user`) always produces a
partial record, never `certificate/recheck.txt` itself. Run it locally before every push
regardless -- the kernel-replay half is still real local evidence even where Comparator cannot run
-- but adopt the canonical complete record from CI when you need one:

```bash
gh workflow run verify.yml --ref <branch>
bash framed_channel/scripts/adopt-recheck.sh
git add framed_channel/certificate/recheck.txt && git commit
```

See [framed_channel/certificate/README.md](../framed_channel/certificate/README.md)'s
"recheck.txt" for the full completeness/PARTIAL/adopt-recheck story (what each `produced on:` and
`record:` field means, why a partial record can never be mistaken for a complete one, and what
`adopt-recheck.sh` validates) and
[framed_channel/recheck/README.md](../framed_channel/recheck/README.md) for platform prerequisites
and the two Comparator pins.

## Pinned versions

One merged table: every pinned dependency, its value source and policy, and how (and by what
mechanism) it gets bumped. What a pin move means for a version number -- the BUMP/HOLD split
below maps to no-bump vs. minor -- is stated in
[docs/consuming.md](consuming.md#what-not-to-build-against).

| Pin | Value source | Policy | Mechanism | Automated/Manual |
|---|---|---|---|---|
| Aeneas (`nix/aeneas-pin.json`, `flake.lock` `.nodes.aeneas`, `framed_channel/aeneas/lakefile.toml` `rev`, `framed_channel/aeneas/lake-manifest.json`) | see `nix/aeneas-pin.json`'s `tag`/`rev` | **BUMP** weekly (see "Pin bump procedure" below). `aeneas.url` in `flake.nix` carries no ref at all (floating on the default branch); the pin file plus `flake.lock`'s locked rev are what actually fix the revision -- `aeneas_rev_coherence` catches an accidental `nix flake update aeneas` that moved the lock without the pin file, and also checks the `lakefile.toml`/`lake-manifest.json` pair | [`nix/bump-aeneas-pin.sh`](../nix/bump-aeneas-pin.sh) + [`update-aeneas-pin.yml`](../.github/workflows/update-aeneas-pin.yml): weekly, the middle rule with a 30-day cap (see "Pin bump procedure" below) | **Automated** |
| Charon (`nix/aeneas-pin.json`'s `charon_rev`) | read from the Aeneas release bundle | Moves in lockstep with the Aeneas pin; never independently pinned, and Charon *nightly* releases are never used as a source (see "Charon/Aeneas provenance" below) | moves automatically with the Aeneas pin above, read from the release bundle at bump time | **N/A** -- see the Aeneas row |
| nixpkgs, rust-overlay (`flake.lock`) | see `flake.lock` | **BUMP** weekly; held fixed while investigating an Aeneas pin move, then relocked once the move is proven stable | [`update-flake-inputs.yml`](../.github/workflows/update-flake-inputs.yml): weekly `nix flake update nixpkgs rust-overlay`, gated in-job by `nix flake check --all-systems` plus a real `bash full-gate.sh --yes` before opening a PR | **Automated** |
| Comparator, `lean4export` (`nix/comparator-pin.json`, `framed_channel/recheck/lakefile.toml` `rev`), `nix/lean-toolchain-bin.nix` (Comparator's own Lean, `lean_toolchain_version`/`lean_toolchain_assets` in the same pin file) | see `nix/comparator-pin.json`'s `rev`/`lean4export_rev` (currently Lean v4.34.0 stable); `lean-toolchain-bin.nix` bumps together with it | **BUMP** was applied to move off the v4.34.0-rc2 track; further bumps are a manual task -- the pin-bump procedure below (step 2), whose gate-and-evidence step requires a green `full-gate.sh --yes`/`--recheck --yes` pair, is the check that recheck verdicts stayed correct. The pin file is the single source; the lakefile `rev` is the one hand-synced duplicate, checked by `recheck_pin_coherence` | edit the pin file plus the one hand-synced Lake literal (step 2 of the procedure below); the local aarch64-linux comparator/lean-toolchain-bin smoke recipe follows automatically, since it reads the pin file with `jq`, never a literal | **Manual** |
| Project Lean (`framed_channel/{lean,aeneas,recheck}/lean-toolchain`) | v4.31.0 | **HOLD**. See "one Lean for both?" below | a maintainer edits `lean-toolchain` (updating `nix/lean-toolchain-pin.json` in the same commit when the toolchain tag itself moved), then gates locally | **Manual** |
| Mathlib (`framed_channel/aeneas/lake-manifest.json`) | tracks whatever `lake update --keep-toolchain aeneas` resolves | **HOLD** unless an Aeneas pin move drags it (a ~7 GB re-fetch; recorded in that bump's commit body when it happens) | a maintainer runs `lake update --keep-toolchain aeneas`, then gates locally | **Manual** |
| `LEAN4LEAN_REV`, landrun (`nix/landrun.nix`), `rust-toolchain.toml` (project Rust, 1.95.0) | see the respective file | **HOLD**. Bumping any of these is a separate, manual task; none is coupled to the Aeneas pin | a maintainer edits the pin directly, then gates locally | **Manual** -- none is in scope for Dependabot's `github-actions`-only ecosystem or `update-flake-inputs.yml`'s `nixpkgs`/`rust-overlay`-only scope |
| Every GitHub Action SHA (`uses: owner/repo@<sha>` across `.github/workflows/*.yml` and `.github/actions/*/action.yml`) | see the respective file | **BUMP** weekly | [`.github/dependabot.yml`](../.github/dependabot.yml): `github-actions` ecosystem, weekly, grouped into one PR | **Automated** |
| The Nix installer release used on x86_64-darwin | **not a pin in this repository** | **N/A** -- upstream's choice; see [docs/ci.md](ci.md#known-coverage-gaps) for the standing decision to retire the Intel legs rather than pin them | `nix-installer-action` selects it itself on Intel macOS, falling back to the last Intel-supporting release. No `source-tag` input is passed anywhere, deliberately: an action *input* is not a `uses:` SHA, so Dependabot's `github-actions` ecosystem would not see it, and it would become the one version in the tree no mechanism in this table owns. [`intel-installer-smoke.yml`](../.github/workflows/intel-installer-smoke.yml) detects the day that fallback disappears, on the Dependabot PR that removes it | **N/A** -- upstream's choice |

**One Lean for both? No.** The project's own Lean toolchain (v4.31.0, used by
`framed_channel/{lean,aeneas,recheck}`) and Comparator's Lean (built by
`nix/lean-toolchain-bin.nix`, currently 4.34.0 stable) are deliberately independent pins. Comparator
is an external, independently-versioned kernel checker consumed only through
`framed_channel/recheck` (a separate Lake package with its own `lean-toolchain`); unifying the two
would mean either holding the project back to whatever Lean version Comparator's own release
schedule allows, or forking Comparator to track an unreleased Lean, neither of which is worth the
project's own Mathlib-driven upgrade cadence. `recheck_rev_coherence` does not check these two
against each other at all (they simply never need to match); it checks two other things:
that `recheck/lean-toolchain` agrees with `lean/lean-toolchain` and `aeneas/lean-toolchain` (the
project's own three Lake packages must share one toolchain), and that the built `lean4lean`/
`lean4export` binaries under `recheck/` embed the project's own Lean githash rather than
Comparator's kernel Lean githash -- catching an accidental cross-contamination between the two
independent pins, not a drift toward matching them.

**Aeneas float-and-relock policy.** `aeneas.url` in `flake.nix` is `github:AeneasVerif/aeneas`, no
ref at all (floating on the repository's default branch), but this is misleading in isolation: `flake.lock` pins a specific revision of that
floating URL, and `nix/aeneas-pin.json` independently records the SAME revision plus everything
the prebuilt route needs to reproduce it (the release tag, the three per-system asset hashes, the
bundled Charon revision and Rust nightly). `aeneas_rev_coherence` fails loudly if the two ever
disagree (an accidental `nix flake update aeneas` without updating the pin file, or vice versa).
The float exists only so `nix/bump-aeneas-pin.sh`'s `nix flake lock --override-input aeneas
github:AeneasVerif/aeneas/<rev>` can relock to an arbitrary future revision without editing
`flake.nix` itself.

### Charon/Aeneas provenance

Charon and Aeneas come from **upstream's own release bundle** (a `nightly-YYYY.MM.DD-<sha>` GitHub
release on `AeneasVerif/aeneas`), never from a Charon nightly release directly and never built from
source by default. Each release tarball bundles `aeneas`, `charon`, `charon-driver`, the exact
`rust-toolchain` those binaries were built against, and (except where noted) a
`lean-build-aeneas-*` archive -- Lake's own release-build accelerator, unrelated to this
repository's own build. `nix/aeneas-pin.json`'s `charon_rev` is read from the bundle's own `charon
version` output and must equal that Aeneas revision's own `charon-pin` file -- this is what "moves
in lockstep" means above: there is no independent Charon revision to bump. That equality is
upstream's release process, not something a Nix derivation can enforce, so it is checked twice:

- **at bump time**, `nix/bump-aeneas-pin.sh` reads the candidate revision's upstream `charon-pin`
  and treats a candidate whose bundled `charon version` differs from it -- or whose `charon-pin`
  cannot be read -- as ineligible, before it can cost a gate;
- **at gate time**, `aeneas_rev_coherence` compares `charon version` on `PATH` with
  `nix/aeneas-pin.json`'s `charon_rev`, and `charon_rev` with the fetched Aeneas sources'
  `charon-pin`.

Every `aeneas_rev_coherence` verdict is a function of pinned, committed inputs only. The fetched
checkout under `framed_channel/aeneas/.lake/packages/aeneas` is mutable state, so it is consulted
only when its `HEAD` equals the manifest's aeneas revision; a stale one prints `[skip] fetched
Aeneas sources are at <x>, manifest pins <y> (stale checkout; lake will update it)` and can never
produce a `[FAIL]`. `check.sh --committed-extraction` passes `--no-binaries`: it never invokes
charon or aeneas, so binaries of those names that happen to be on `PATH` (a user profile's, from
another pin) are reported as `[skip]`, not compared.

**Per-system availability at the current pin**: see `nix/aeneas-pin.json`'s `assets` object (a
`null` entry means no prebuilt asset for that system at the current pin; `full-gate.sh`'s
per-machine fallback chain -- see "Running the full gate locally (opt-in)" above -- applies there).
**Why not Charon nightlies**: see [`nix/aeneas-prebuilt.nix`](../nix/aeneas-prebuilt.nix)'s header
("Why the Aeneas release, never a Charon nightly release").

## Availability without a binary cache

A fresh clone needs no account, token, or third-party/owned binary cache to reach a green gate.
Every input the Nix-driven gate itself fetches is either a hash-pinned, fixed-output download or
served by
`cache.nixos.org` -- Nix's own default substituter, unchanged and unconfigured anywhere in this
repository (`flake.nix` carries no `nixConfig` substituters block, and no workflow or script adds
an `extra-substituters` entry). One input outside the Nix store falls outside that guarantee: the
elan-downloaded Lean toolchain (elan fetches a GitHub release directly, not through a Nix
substituter; a fresh download is checked cryptographically against
`nix/lean-toolchain-pin.json`'s committed per-system sha256 before elan installs it
(`nix/lean-toolchain-pin.sh`, run from `full-gate.sh` and the `lean-toolchain` composite action
on a cache miss) -- the pre-existing `lake --version`/`lean --version` probe in the
`lean-toolchain` action only proves the installed toolchain runs, which is a different claim from
verifying the bytes elan fetched).

**Per input class:**

| Input | Availability guarantee |
|---|---|
| Charon/Aeneas (`nix/aeneas-prebuilt.nix`) | sha256-pinned, fixed-output download of a GitHub Release tarball named in `nix/aeneas-pin.json`'s `assets` object -- content-addressed, never silently substituted, no cache dependency by construction |
| The Rust nightly the pin names (`nix/aeneas-pin.json`'s `rust_nightly`) | rust-overlay, resolved from `cache.nixos.org` |
| nixpkgs closures | `cache.nixos.org` |
| The MIR sysroot (`nix/mir-sysroot.nix`) | not a download at all: a local, offline `runCommand` build (`cargo miri setup`) from the pinned Rust nightly's vendored sources, so it needs no substituter or network access |
| Lake packages (Mathlib, Aesop, Batteries, proofwidgets, etc.; `framed_channel/{lean,aeneas,recheck}/lake-manifest.json`) | commit-pinned `git` clones from GitHub; GitHub retains any commit reachable from a ref indefinitely |
| Mathlib's `lake exe cache get` build cache | convenience only, not load-bearing (see "Cache strategy" in [docs/ci.md](ci.md)); a miss retries three times, then falls back to compiling Mathlib from source -- correct, only slower |
| The Lean toolchain (elan-downloaded) | not from `cache.nixos.org`: elan fetches the release named in `lean-toolchain` directly from GitHub, outside the Nix store; a cache-miss fetch is checked against `nix/lean-toolchain-pin.json`'s committed per-system sha256 before elan installs it, and the `lean-toolchain` action separately verifies `lake`/`lean` run, self-healing once on a broken install (see [docs/ci.md](ci.md#cache-strategy)) |
| `nix/lean-toolchain-pin.json` (the Lean toolchain's own pin) | not a download itself -- the committed per-system sha256 digests `nix/lean-toolchain-pin.sh` checks a fresh elan-fetched asset against; pins bytes, not availability (see "Retention risk and mitigation" below) |

**Local coverage of the Lean toolchain pin check is limited to `full-gate.sh`.** A toolchain elan
installs some other way -- a bare `lake build` inside a Nix dev shell, or the
[non-Nix path](setup-without-nix.md) -- is not checked automatically: the check does not live in
`check.sh` itself, because `check.sh` is a certificate-identity input
(`scripts/certificate-identity.sh`'s `identity_file_list`), and adding a network-touching check
there would change the tree's identity on every run. `bash nix/lean-toolchain-pin.sh` (needs
`jq`, `curl`) is the manual equivalent for those paths.

**Retention risk and mitigation.** A sha256 pin only guarantees that *if* the pinned asset is
fetched, it is the exact bytes recorded -- it says nothing about whether that asset is still there
to fetch. The pinned Aeneas release tarball is the one input class with a real (if low-probability)
retention risk, since upstream *could* delete an old nightly; see
[Troubleshooting](#troubleshooting)'s "If the pinned Aeneas release asset disappears" entry for the
three mitigations.

**Continuously verified, not audited once.** "Nothing silently builds from source" is not a
one-time claim -- it is enforced on every CI run by `nix/heavy-build-probe.sh` (`verify.yml`'s
"Substituter probe" step, and every `verify.yml`/`ci-macos-gate.yml` job that resolves a route through
`full-gate.sh`), which classifies every store path a resolved shell would realize and fails loudly
(`PROBE_SOURCE` non-empty) on an unexpected from-source charon/aeneas build. The scheduled
fresh-clone canary (see [docs/ci.md](ci.md#platform-matrix)'s Platform matrix) runs the same probe on a cold clone,
so this guarantee is checked on a recurring cadence, not just at merge time.

## Pin bump procedure

One scripted, documented sequence, whether run by the weekly `update-aeneas-pin.yml` workflow or
by hand:

1. **`bash nix/bump-aeneas-pin.sh`** (or let the weekly PR do it). The **middle rule, stated
   exactly**: pick the newest Aeneas nightly release with prebuilt assets for every supported
   system (x86_64-linux, aarch64-linux, aarch64-darwin) -- "complete" -- that passes the gate. If
   that complete release's tagged commit is dated **more than 30 days** (inclusive boundary: 2,592,000
   seconds is still "within") before the newest release with just the two Linux assets --
   "Linux-complete" -- that passes the gate, take the Linux-complete release instead and flag that
   macOS is on its fallback chain (`nix/aeneas-pin.json`'s `macos_fallback: true`). Selection is
   **stateless** and may move the pin **backward** (to an older commit) when that is what the rule
   picks; this is expected, not a bug. `--check-only` reports what the rule would pick without
   writing anything; see `bash nix/bump-aeneas-pin.sh --help` for every flag.

   Each visited candidate is applied and gated in place with `check.sh --skip-approvals`: every
   stage runs except approvals -- `aeneas_rev_coherence`, the extraction/candidate staleness
   check, the core and bridge packages, the proof ladder, cargo fmt/clippy/test. Approvals is
   skipped here by design, not weakened: any candidate that moves `charon_rev` changes
   `candidates.txt`'s `# charon:` header, which stales the recorded `candidates_sha256` whether or
   not the candidate is otherwise good, so a stale-approvals failure is never a reason to reject a
   candidate during selection. `--skip-approvals` is internal to this script's own gate (see
   `check.sh --help`) and is never itself the verification claim; re-approval happens right after
   selection, in step 5 below, and the search's summary JSON's `gate_failures` array names every
   candidate the search tried and rejected at the gate, with the stage that failed -- see "When
   the search reports a gate failure" below for the one kind of gate failure that needs a person
   (or agent) to intervene rather than just moving on to the next candidate.
2. **The Comparator pin bump** (only when bumping Comparator itself, independently of the
   Aeneas pin -- see the "Pinned versions" table's HOLD/BUMP split above): edit
   `nix/comparator-pin.json` (the single source of truth -- `rev`, `src_hash`,
   `lean4export_rev`, `lean4export_src_hash`, `lean_toolchain_version`, `kernel_githash`,
   `lean_toolchain_assets`), then `framed_channel/recheck/lakefile.toml`'s lean4export `rev`
   literal (the one duplicate Lake TOML cannot source from the pin file), then `cd
   framed_channel/recheck && lake update --keep-toolchain` to regenerate `lake-manifest.json`.
   The local aarch64-linux comparator/lean-toolchain-bin smoke recipe (build
   `.#packages.aarch64-linux.{comparator,lean-toolchain-bin}` on an aarch64 host and check
   `lean --version`; not a CI job -- `verify.yml`'s `recheck` job already exercises both packages
   on every filtered push, via `full-gate.sh --recheck --yes` on its aarch64-linux leg) follows
   automatically too -- it reads `nix/comparator-pin.json`'s `lean_toolchain_version` with `jq`,
   never a literal.
3. **When Comparator moved**: `recheck_pin_coherence` (build-free; runs in `check.sh`'s default
   path, not only under `--recheck`) followed by `recheck_rev_coherence` -- both must be `[ok]`
   before proceeding. (`aeneas_rev_coherence` already ran as part of step 1's own gate and needs
   no separate check here.)
4. **`bash full-gate.sh --recheck --yes`**, so the recheck record matches the new identity -- the
   one stage step 1's gate does not run. When the new pin has a darwin asset, also dispatch
   `ci-macos.yml`'s `aeneas-prebuilt` job (`gh workflow run ci-macos.yml --ref <branch>`) -- a
   dedicated, fast runtime check of the darwin re-sign path (`install_name_tool` +
   `autoSignDarwinBinariesHook` in `nix/aeneas-prebuilt.nix`). `ci-macos-gate.yml`'s
   `aeneas-gate` job exercises the same re-signed package too, at the current pin (it runs
   `full-gate.sh --yes`, which resolves to the prebuilt route whenever the pin has a darwin
   asset), but `aeneas-prebuilt` is the narrower, purpose-built probe to dispatch here.
5. **Regenerate the certificate and re-approve**: any pin change alters the certificate identity
   (see "Certificate regeneration" above). This step is reachable right after step 1's gate
   succeeds -- its approvals-stage skip is exactly what leaves this the one remaining stale item.
   Run `bash framed_channel/approve.sh --review --aeneas` and `--record` any item it reports
   stale, attributing each one to the specific pin-driven diff that staled it (most commonly just
   the `# charon:` header change in `candidates.txt`).
6. **One commit** covering the pin files, the regenerated extraction/candidates (when Aeneas
   moved), the certificate, and any re-approval. When driven by the weekly workflow instead of by
   hand, the opened PR's checklist includes this re-approval; `verify.yml`'s own approvals stage
   fails on the PR until it is checked off and the re-approval commit is pushed.

**When the search reports a gate failure.** A failure the search hits and moves past (trying the
next candidate, or falling back to Linux-complete) shows up in `gate_failures`, by candidate tag
and failing stage, in both the summary JSON and the weekly workflow's step summary -- including on
an otherwise-green "already current" run, since a by-design failure worked around during the
search is still worth seeing. Most stages that can fail this way (a Lean/Rust build error, a
failing proof, a lint) mean the candidate itself is broken and the search is right to reject it.
One stage is different: a failure at `refresh-extraction.sh`'s externals check means upstream
renamed, removed, or added a trusted external -- a hand-written file under
`framed_channel/aeneas/FramedChannelAeneas/Extracted/` (e.g. `FunsExternal.lean`) that no longer
agrees with the regenerated extraction template. The search cannot fix this itself: matching a
renamed external is a judgment call about what the new name means, not a mechanical edit, so it
is never made automatically, and `refresh-extraction.sh`'s exact-name comparison stays exact
rather than fuzzy for exactly this reason. Adopt such a candidate by hand instead. First confirm
the rule would actually select it: `nix develop .#build --command bash nix/bump-aeneas-pin.sh
--check-only` runs the same rule with every gate treated as passing, and there is no flag that
forces one release (`--tag` only reports). If it names the rejected candidate, `--apply-ungated`
writes the pin/lock/lakefile files for it without gating it; edit the externals file to the names
the regenerated template (and `Funs.lean`, after `refresh-extraction.sh`) actually need; re-run
`refresh-extraction.sh`, then `refresh-candidates.sh`, then `check.sh --skip-approvals` until
green; then steps 4-6 above (recheck, re-approve, one commit) as usual. If `--check-only` names a
different release, or reports "already current", the rejected candidate was Linux-complete only
and the rule prefers a complete release inside the 30-day window (possibly the current pin) over
it -- so there is nothing to adopt yet, and the same gate failure will be reported every week
until upstream publishes a darwin asset for a release at or after that commit, or the window runs
out and the rule falls back to it with `macos_fallback: true`. Do not hand-edit
`nix/aeneas-pin.json` to get around this. A gate failure at any other stage is never adopted by
hand this way -- it means the candidate is genuinely broken, not that the search fell short.

**Pin-file pattern.** Both multi-consumer pins in this repository (Aeneas, Comparator) follow the
same shape: a single JSON file under `nix/` is the source of truth (`nix/aeneas-pin.json`,
`nix/comparator-pin.json`), read by every Nix derivation that needs it with `builtins.fromJSON
(builtins.readFile ...)` and by every shell script that needs it with `jq`. The one place this
shape cannot reach is a Lake package's own `lakefile.toml`, which has no mechanism to read an
external file -- Lake resolves `[[require]]` `rev`s from the TOML text itself, at `lake update`
time. That literal stays a hand-synced duplicate of the pin file's revision, caught by a
coherence check (`aeneas_rev_coherence`, `recheck_pin_coherence`) that fails loudly, build-free,
whenever the two disagree. A future pinned dependency that needs the same treatment: add a
`nix/<name>-pin.json`, wire it into every Nix/shell consumer, add its one Lake-literal coherence
check if it has a Lake package, and add the pin file to
`framed_channel/scripts/certificate-identity.sh`'s `identity_digest_lines` if it is a
certificate-identity input.

**A nixpkgs relock invalidates the `~/.elan` CI cache by design** (its key carries the locked
nixpkgs revision; see [docs/ci.md](ci.md#cache-strategy)), and can break a local `~/.elan` the
same way once the old store paths are garbage-collected -- see
[Troubleshooting](#troubleshooting) below.

The from-source fallback for a pin that lacks a prebuilt asset for your system is
`bash full-gate.sh --source` (~30 min, ~12 GiB after a cost prompt) -- see "Running the full gate
locally (opt-in)" above for the full fallback chain.

### How every pin is proposed

Merged into the single table under [Pinned versions](#pinned-versions) above (its Mechanism and
Automated/Manual columns), so every pinned dependency's value, policy and bump mechanism are read
from one place.

**Manual-row procedure and evidence.**

- **Lean toolchain / Mathlib**: edit the toolchain file (or run the `lake update` command above).
  When the toolchain tag itself moved (not just Mathlib), update `nix/lean-toolchain-pin.json`'s
  `lean_toolchain` and its `assets` in the **same commit**:
  `gh api repos/leanprover/lean4/releases/tags/<new-tag> --jq '.assets[] | {name, digest}'` gives
  the per-system sha256 (the API's `digest: sha256:<hex>` field, stored as lowercase hex, not
  Nix's SRI form -- see the pin file's own comment in `nix/lean-toolchain-pin.sh`); one entry per
  system that publishes the matching `lean-<version>-<os>[_<arch>].tar.zst` asset. `bash
  nix/lean-toolchain-pin.sh --check-consistency-only` fails loudly, before any gate run, if the
  pin and the toolchain files disagree -- this is not a separate reminder, it is the same check
  `full-gate.sh` runs on every local invocation. This bump is not coupled to the weekly Aeneas
  pin bump; it happens whenever the Lean toolchain itself moves. Then run `bash full-gate.sh
  --yes` and `bash full-gate.sh --recheck --yes` locally. Evidence to accompany the change: a
  green local full gate (both commands above exit 0), and, where the certificate identity
  changed, a regenerated certificate with `bash framed_channel/approve.sh --review
  --aeneas`/`--record ... --aeneas` resolving every item it reports stale (see "Certificate
  regeneration" above).
- **Comparator**: perform the pin bump named in step 2 of the procedure above (edit
  `nix/comparator-pin.json`, then `framed_channel/recheck/lakefile.toml`'s lean4export `rev`
  literal, then `lake update --keep-toolchain` to regenerate `lake-manifest.json`; the local
  aarch64-linux smoke recipe and `nix/comparator.nix`/`nix/lean-toolchain-bin.nix` follow
  automatically from the pin file), then the same gate-and-evidence requirement as the Lean
  toolchain/Mathlib row: a green `full-gate.sh --yes`/`--recheck --yes` pair, and a regenerated,
  re-approved certificate if the identity moved.

**The `GITHUB_TOKEN`-opened-PR limitation**: see [docs/ci.md](ci.md#known-coverage-gaps) for the
full explanation and what a maintainer does about it.

## Troubleshooting

**If the pinned Aeneas release asset disappears** (upstream deletes an old nightly -- a
low-probability but real risk for a named GitHub Release asset). Three mitigations, none of which
needs an account, token, or third-party cache:

1. The weekly pin-bump policy keeps the pin recent by construction (the middle rule, stated in
   full in [Pin bump procedure](#pin-bump-procedure) above), rather than ever aging toward a
   hypothetical retention boundary on an old, unmaintained tag.
2. The consented from-source fallback: `full-gate.sh` degrades to `--source` (~30 min, ~12 GiB,
   cost-prompted), rebuilding the exact locked revision (`flake.lock`'s `.nodes.aeneas`) from the
   `aeneas` flake input's own source -- a rebuild, not a substitution.
3. The committed-extraction pre-check (`check.sh --committed-extraction`) never needs
   charon/aeneas at all -- it audits the already-committed extraction and prints `INCOMPLETE`
   rather than certifying, so a fresh clone always has *some* working path even if both the
   prebuilt asset and the from-source route were somehow unavailable.

**`error: command failed: 'lake'` / `No such file or directory (os error 2)`** (or the same for
`lean`), from a `lake` that is plainly on `PATH`. elan's `lake` is a proxy that execs the installed
toolchain's real binary, and on Linux nixpkgs' elan patches every toolchain it installs so that
its ELF interpreter and `cc` wrapper are `/nix/store` paths of the nixpkgs revision that installed
it. After a nixpkgs relock followed by a garbage collection (or with a `~/.elan` copied or restored
from elsewhere) those paths are gone, and the kernel reports the missing interpreter as if the
binary itself were missing. `check.sh` probes for this before building anything and names it;
the remedy is

```bash
elan toolchain uninstall "$(cat framed_channel/lean/lean-toolchain)"
```

then re-enter the dev shell and re-run: elan reinstalls the toolchain against the current nixpkgs.
In CI the `lean-toolchain` composite action does the same thing once, automatically, and reports
`healed: true` in the step summary.

**`bash full-gate.sh` or `bash install.sh` fails immediately on macOS.** Both run under the stock
`/bin/bash` 3.2 by design; `bash framed_channel/tests/launcher-compat/run.sh` reports the file and
line of any construct that does not. Every other script runs inside a Nix dev shell and may
assume bash >= 4.4.

**Comparator passes locally and fails on a runner** (`[landrun:error] ... permission denied`,
`failed to remove output artifacts ... AeneasMeta/Utils.olean`, or any other difference inside a
room). A hosted runner differs from a development host in which elan installed the toolchain
(nixpkgs' elan patches the ELF interpreter and wraps `lake`) and in `CI=true` (Aeneas's lakefile
precompiles `AeneasMeta` only where `CI` is unset, cached in `.lake/config` at elaboration time);
see [framed_channel/certificate/README.md](../framed_channel/certificate/README.md)'s "sandbox
deviations" bullet for the full explanation of what each grant means and why. To run the rooms
exactly as a runner does, without touching `~/.elan`:

```bash
export CI=true ELAN_HOME="$(mktemp -d)"   # the dev shell's elan installs the pinned toolchain into it
a=framed_channel/aeneas/.lake
mv "$a/config" "$a/config.host"           # Lake re-elaborates every lakefile under CI=true
mv "$a/packages/aeneas/backends/lean/.lake/build" "$a/packages/aeneas/backends/lean/.lake/build.host"
nix develop .#recheck --command bash -c '
  (cd framed_channel/aeneas && lake exe cache get && lake build) &&
  bash framed_channel/scripts/recheck-comparator.sh --out "$(mktemp -d)" --bridge'
```

Move the two `.host` directories back afterwards (delete the ones the run created first). It
needs `framed_channel/aeneas/.lake/packages` fetched and the `recheck/` tools built, which a
previous `full-gate.sh --recheck --yes` leaves in place; it writes nothing tracked into the tree.
On a red `recheck` job (either leg), `gh run download <run> -n recheck-diagnostics` (x86_64-linux)
or `-n recheck-diagnostics-arm` (aarch64-linux) holds every room log and the shim's log.

## Close-out after a green run

The ordered close-out once a push has produced green runs, and the checklist after publishing,
forking or transferring the repository (when no workflow has run yet). Pushing, dispatching a
workflow and committing the adopted record are a maintainer's own actions.

1. Push to `main`, or open a pull request against it. No workflow commits to `main`, so a plain
   `git push` is enough. Every trigger here is `branches: ["main"]` only, so a push to any other
   branch with no open pull request runs nothing.
2. Confirm `ci.yml` is green (every admitted push runs it): both Linux `build` legs and
   `hygiene`. `ci-macos.yml` -- `launcher-compat` on both darwin architectures, `build` and
   `aeneas-prebuilt` -- no longer runs on a push; it must be requested (see
   [docs/ci.md](ci.md#macos-runs-on-request-only)): `gh workflow run ci-macos.yml --ref <branch>`.
3. Confirm every leg of `verify.yml`'s two push jobs -- `verify` and `recheck`, each an
   x86_64-linux/aarch64-linux matrix -- is green: a push that touches their inputs runs them by
   itself (see
   [docs/ci.md](ci.md#trigger-policy)); otherwise force a full run: `gh workflow run verify.yml
   --ref <branch>`. `ci-macos-gate.yml`'s `aeneas-gate` and `ci-macos-recheck.yml`'s
   `recheck-kernel` are on request only now -- no push ever admits them -- so dispatching is the
   *only* way to run them, not a fallback: `gh workflow run ci-macos-gate.yml --ref <branch>`,
   `gh workflow run ci-macos-recheck.yml --ref <branch>`.
4. After a publication, fork or transfer only: dispatch each schedule- or dispatch-only workflow
   once, `setup-without-nix.yml` if the push did not admit it, and confirm every leg green:
   `gh workflow run fresh-clone-canary.yml`, `gh workflow run setup-without-nix.yml`,
   `gh workflow run update-aeneas-pin.yml`, `gh workflow run update-flake-inputs.yml`. The last two
   need the repository setting in [docs/ci.md](ci.md#repository-settings) and end in either a pull
   request or an "already current" summary; both are a pass. `intel-installer-smoke.yml` is not
   part of this publication-only step: it normally runs automatically, path-filtered to its own
   file, on the next Dependabot PR that bumps the installer action (see
   [docs/ci.md](ci.md#macos-runs-on-request-only)) -- confirm it ran green on the last such PR, or
   dispatch it directly if none has landed yet: `gh workflow run intel-installer-smoke.yml --ref
   <branch>`.
5. Adopt the CI-produced recheck record: `bash framed_channel/scripts/adopt-recheck.sh --run <ID>`
   (the run ID of the green `verify.yml` run from step 3 -- see
   `bash framed_channel/scripts/adopt-recheck.sh --help` for `--run`/`--from`/`--dry-run`), review
   `git diff -- framed_channel/certificate/recheck.txt`, then
   `git add framed_channel/certificate/recheck.txt && git commit`.

**Why step 5 is real work, not a formality**: a `framed_channel/certificate/recheck.txt`
committed from a local gate run was produced locally (its `produced on:` line reads
`Linux x86_64 (local)`), while the canonical, complete record carries the `CI: verify.yml recheck
job` producer line that only a real hosted run writes (see "The independent recheck" above).
`adopt-recheck.sh` refuses anything that is not a `record: complete`, identity-matching candidate
-- re-running the gate locally again cannot satisfy it; only a genuine CI run can. The `--from
FILE` path enforces this itself now, not just by convention: it rejects a candidate whose
`produced on:` line does not name one of `verify.yml`'s two CI producers (`verify.yml recheck
job`/`verify.yml recheck-arm job`), so a locally-produced record cannot be smuggled in that way
either.

**What CI does and does not commit** (this repository's standing posture, stated once here):
every step above -- the push, every dispatch, and the `adopt-recheck.sh` review and commit -- is a
human's own action, and no workflow ever commits anything to `main`: not source, certificate, pin
or documentation changes, and not a badge either (the README's badges are GitHub's own, served
from each workflow's latest run; see [docs/ci.md](ci.md#overview)). The automated pin-bump
workflows open pull requests and never push to `main`; see this file's own "Pin bump procedure"
and "How every pin is proposed" sections above.

## Navigation

- [docs/README.md](README.md)
- [docs/ci.md](ci.md)
- [Back to README](../README.md)
