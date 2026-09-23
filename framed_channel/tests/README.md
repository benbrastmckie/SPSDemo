# tests/

Fixture tests for the gate's tools and the two outside-Nix launchers. `../check.sh` does not run
them; CI does. Each runner accepts `--help`, works in a temporary
directory, and exits 0 when every case behaves as recorded, 1 otherwise, 2 on a usage error.

Each `<dir>/run.sh`'s own header carries the full case list; this table names only what each
suite covers and points there for the rest.

| Directory | Tests | Fixtures |
|---|---|---|
| `approvals/` | `check-approvals.sh` and `approve.sh --record`'s refusals, plus `source_sha256`'s version-independence -- see `approvals/run.sh` | `*.yaml` cases with stand-in `candidates.txt`/`spec*.records`; a throwaway `rust/` tree for the version-independence cases |
| `ladder/` | the proof-method ladder in `lean/FramedChannel/Ladder.lean` -- see `ladder/run.sh` | `*.lean` cases elaborated with `lake env lean` |
| `layer/` | `../check.sh`'s layer import rules: both halves of each rule (the import that must be rejected, and the one that must not be), plus the assertion that no rule types a component name -- see `layer/run.sh` | module paths and import lists, matched by check.sh's own extracted `layer-rules` block |
| `aeneas-revs/` | `aeneas_rev_coherence` (`scripts/lib/aeneas-revs.sh`) -- see `aeneas-revs/run.sh` | a throwaway tree with fake `aeneas`/`charon` on `PATH` |
| `recheck-revs/` | `recheck_pin_coherence` and `_recheck_load_pin` (`scripts/lib/recheck-revs.sh`) -- see `recheck-revs/run.sh` | a throwaway tree with its own copy of `recheck-revs.sh` |
| `recheck-record/` | `scripts/recheck-record.sh`'s verdict-to-record rendering, including a golden check against the real committed `certificate/recheck.txt` -- see `recheck-record/run.sh` | canned verdict/deviation text; the golden case reads the committed record via `git show` |
| `cert-freshness/` | `scripts/certificate-freshness.sh`'s strict and `--portable-host` comparisons -- see `cert-freshness/run.sh` | throwaway git repositories |
| `landrun-shim/` | `recheck/landrun-shim.sh`'s `CI`-variable hand-down to a Comparator room -- see `landrun-shim/run.sh` | a stub `landrun`; Linux only |
| `bump-pin/` | `../../nix/bump-aeneas-pin.sh`'s candidate walk and eligibility rules -- see `bump-pin/run.sh` | canned release/bundle JSON; no network |
| `lean-toolchain-pin/` | `../../nix/lean-toolchain-pin.sh` -- see `lean-toolchain-pin/run.sh` | canned pin JSON and local files; no network |
| `full-gate/` | `../full-gate.sh`'s fallback chain, consent rules and `--support-level` on all four systems -- see `full-gate/run.sh` | a stub `nix` and stub pin files |
| `launcher-compat/` | `full-gate.sh`/`install.sh`/the two composite actions' scripts stay runnable under the host bash -- see `launcher-compat/run.sh`. The faithful macOS run is `ci-macos.yml`'s `launcher-compat` job, on request (see [../../docs/ci.md](../../docs/ci.md#macos-runs-on-request-only)) | none (a stub `nix` built at run time) |
| `spdx/` | `scripts/check-spdx.sh` outside a git work tree -- see `spdx/run.sh` | small trees built at run time |
| `ci-docs-coherence/` | `scripts/check-ci-docs-coherence.sh`'s twelve `docs/ci.md` <-> `.github/` structural invariants -- see `ci-docs-coherence/run.sh` | small `--root` trees (two workflows, one composite action, a minimal `docs/ci.md`) built at run time |
| `certificate-identity/` | `scripts/certificate-identity.sh`'s digest and identity checks, including `cargo_version_normalized_sha256`'s version-scoping -- see `certificate-identity/run.sh` | a throwaway tree with its own copy of `certificate-identity.sh` and realistic `rust/Cargo.toml`/`rust/Cargo.lock` fixtures |
| `adopt-recheck/` | `scripts/adopt-recheck.sh --from FILE`'s validation and refusal cases -- see `adopt-recheck/run.sh` | a throwaway tree with its own copies of `adopt-recheck.sh`/`certificate-identity.sh`; no `gh`, no network |

```
bash tests/adopt-recheck/run.sh   needs bash >= 4.4, coreutils (sha256sum), find
bash tests/aeneas-revs/run.sh   needs bash >= 4.4, jq, git
bash tests/approvals/run.sh     needs bash >= 4.4, coreutils, awk
bash tests/bump-pin/run.sh      needs bash >= 4.4, jq
bash tests/certificate-identity/run.sh   needs bash >= 4.4, coreutils (sha256sum), find
bash tests/cert-freshness/run.sh   needs bash, git, sed, diff
bash tests/full-gate/run.sh     needs bash >= 4.4, jq
bash tests/landrun-shim/run.sh  needs bash, git, ldd, grep, mktemp; Linux only (skips elsewhere)
bash tests/lean-toolchain-pin/run.sh   needs bash >= 4.4, jq, coreutils (sha256sum)
bash tests/launcher-compat/run.sh   needs bash >= 3.2 only; on a machine without /bin/bash (NixOS)
                                set LAUNCHER_COMPAT_BASH="$(command -v bash)" for the dynamic pass
bash tests/ladder/run.sh        needs the Lean toolchain in ../lean/lean-toolchain
bash tests/layer/run.sh         needs bash >= 4.4, coreutils; no Lean toolchain, no build
bash tests/recheck-record/run.sh   needs bash >= 4.4, awk, coreutils; git (optional, for the golden case)
bash tests/recheck-revs/run.sh  needs bash >= 4.4, jq, awk
bash tests/spdx/run.sh          needs bash >= 4.4
bash tests/ci-docs-coherence/run.sh   needs bash >= 4.4
```

## Navigation

- [Parent Directory](../README.md)
