# recheck/

The pinned tools of the independent recheck (`../check.sh --recheck`): a Lake package with no code
of its own, which pins and builds two executables on the project's own Lean toolchain.

| Tool | Revision | Used for |
|---|---|---|
| [Lean4Lean](https://github.com/digama0/lean4lean) | `095c0a947ab870a5dcf0797725a4caec66624285` (builds on v4.31.0) | `../scripts/recheck-kernel.sh`: re-typechecks every declaration the project's modules add, in a Lean-in-Lean kernel |
| [lean4export](https://github.com/leanprover/lean4export) | currently `076e8e57707e813375e8f9da8bf989799ace9680` -- see `../../nix/comparator-pin.json`'s `lean4export_rev` (the revision Comparator's parser is built from, at `.rev`) | `../scripts/recheck-comparator.sh`: Comparator exports the Challenge and Solution environments with it |

## Prerequisites not pinned here

The recheck is two independent verdict producers with different platform requirements (see
`../check.sh --recheck` and `../certificate/README.md`, "recheck.txt", for the full record
format):

- **Kernel replay** (`../scripts/recheck-kernel.sh`: Lean4Lean and leanchecker) runs on any
  platform with the pinned Lean toolchain -- Linux, macOS, any architecture elan supports. It
  needs only the tools built here (`lake build lean4lean/lean4lean lean4export/lean4export`,
  below) and the pinned toolchain (`lean-toolchain`). Exercised on `macos-26` by
  `.github/workflows/ci-macos-recheck.yml`'s `recheck-kernel` job, on request only:
  `gh workflow run ci-macos-recheck.yml --ref <branch>`, with `-f no_cache=true` for a cold run
  with none of this repository's Actions caches restored or saved (see
  [../../docs/ci.md](../../docs/ci.md#macos-runs-on-request-only)).
- **Comparator** (`../scripts/recheck-comparator.sh`) needs a Landlock sandbox, which is a Linux
  kernel feature: on any other platform every config is reported `NOT-RUN`, reason "Landlock
  sandbox is Linux-only" -- never a refusal of the whole recheck, and never silently skipped.
  [Comparator](https://github.com/leanprover/comparator) (a nix build at revision d03acab1) and
  [landrun](https://github.com/Zouuup/landrun) v0.1.17 must be on PATH. On x86_64-linux and
  aarch64-linux, `nix develop .#recheck` provides both (the light `.#default` shell does not --
  see [../../docs/development.md](../../docs/development.md)): they are vendored under
  `../../nix/comparator.nix` and `../../nix/landrun.nix`, exposed as `packages.comparator` and
  `packages.landrun` in the repository's `flake.nix` (`hasComparator`; landrun on every Linux
  system regardless). Comparator's pin (currently `d03acab1`) is single-sourced from
  `../../nix/comparator-pin.json`: `nix/comparator.nix` and `nix/lean-toolchain-bin.nix` read it
  with `builtins.fromJSON`, `../scripts/lib/recheck-revs.sh` reads it with `jq` at source time.
  The one exception is this directory's `lakefile.toml`, whose lean4export `rev` literal Lake
  TOML cannot source from an external file; `recheck_pin_coherence` in
  `../scripts/lib/recheck-revs.sh` checks it against the pin file, build-free, on every
  `check.sh` run.
  Outside the dev shell, pin landrun to v0.1.17 yourself; `nix/landrun.nix`'s header comment says
  why 0.1.15 is insufficient. `.github/workflows/verify.yml`'s `recheck` job runs the full,
  complete aarch64-linux recheck on a genuine `ubuntu-24.04-arm` runner on every filtered push
  (its aarch64-linux leg); a narrower local recipe -- build
  `.#packages.aarch64-linux.{lean-toolchain-bin,comparator}` on an aarch64 host and check
  `lean --version`/`comparator`'s usage output against `nix/comparator-pin.json` -- remains
  available for package-level diagnosis without a full recheck (charon/aeneas have no
  aarch64-linux substituter -- see the repository root `flake.nix`'s header comment).

The Comparator half also needs `jq`, a working `systemd-run --user` and a non-root user; only the
kernel replay's revision-coherence check needs `strings` (binutils).
`../scripts/lib/recheck-revs.sh`'s `aeneas_rev_coherence`/`recheck_rev_coherence` checks each of
these once, up front, before either half runs, including that landrun actually enforces Landlock
on the running kernel, since every landrun call here
is `--best-effort` (strict mode demands Landlock ABI V9 and refuses to start on the ABI v7 kernel
of a hosted runner): a write under `--ro /` must be denied, and a TCP connect with no grant must
fail with EACCES. Under `check.sh --recheck`, a failed revision-coherence check -- including this
landrun probe -- fails the whole run outright (`exit 1`, printing the failure) before either half
starts, so neither `certificate/recheck.txt` nor `recheck.partial.txt` is written; there is no
per-verdict `FAIL` from this probe under `check.sh --recheck`. Run standalone,
`scripts/recheck-comparator.sh` repeats a landrun probe of its own and, on failure, records that
as a `FAIL` verdict for every Comparator config instead of exiting outright -- the two entry
points differ here. A missing tool (in either) makes the affected verdicts `NOT-RUN`, never a
pass. Set `RECHECK_DIAG_DIR=<dir>` on a `check.sh --recheck` run to keep every
log of the recheck (the record keeps only a failure's last line). See
`../certificate/README.md`'s "recheck.txt" section, "hardening" bullet, for what a `NOT-RUN`
Comparator config or a failed probe means for a record's completeness verdict.

**On macOS**: `check.sh --recheck` runs the kernel replay for real and reports Comparator
`NOT-RUN`, so the run is written to the gitignored `../certificate/recheck.partial.txt`, never to
the committed `../certificate/recheck.txt` -- see `../certificate/README.md`'s "recheck.txt"
section for the completeness/provenance record format and why a partial record can never be
mistaken for the canonical one. A macOS contributor obtains a complete, committable record from CI
instead: `../scripts/adopt-recheck.sh` after `gh workflow run verify.yml --ref <branch>` (see
`../../docs/development.md`).

**Seatbelt (`sandbox-exec`) considered, not done**: a macOS-native Comparator sandbox would need
translating Comparator's own landrun invocation (it constructs its own confinement argv; see
`landrun-shim.sh` below) into Seatbelt's very different profile model -- not a small change, and
`sandbox-exec` is itself deprecated by Apple with no stable replacement API. Out of scope here;
the CI-produced record (above) is the portable path to a complete record instead.

## Files

### lean-toolchain
`leanprover/lean4:v4.31.0`, equal to `../lean/lean-toolchain` and `../aeneas/lean-toolchain`. The
tools must be built by the Lean that built the project, so that they read its `.olean` files.

### lakefile.toml
The two `[[require]]` pins. Batteries comes in through Lean4Lean, at the revision
`../aeneas/lake-manifest.json` also locks.

### lake-manifest.json
The resolved pins.

### landrun-shim.sh
The wrapper `../scripts/recheck-comparator.sh` hands Comparator as its landrun. It adds exactly the sandbox
grants the recheck records as deviations; see `../certificate/README.md`, "recheck.txt".

## Building

```
lake build lean4lean/lean4lean lean4export/lean4export     from this directory
```

The first build fetches both repositories and Batteries (network); later builds run offline.
`.lake/` is ignored by git.

**Update only with `lake update --keep-toolchain`.** A plain `lake update` adopts lean4export's own
`lean-toolchain` (a newer Lean) into this package and builds the tools for the wrong Lean.
`../scripts/lib/recheck-revs.sh` catches that: it compares the toolchain files, and checks that each built
binary embeds the project Lean's githash rather than that of Comparator's in-process kernel.

## Navigation

- [Parent Directory](../README.md)
