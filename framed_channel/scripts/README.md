# scripts/

The tools `../check.sh`, `../full-gate.sh` and `../approve.sh` call, plus their shared,
sourced-only `lib/`. One line per file, naming what it does and who calls it -- point at each
script's own `--help`/header for the detail this table does not restate.

| Script | Calls it |
|---|---|
| `adopt-recheck.sh` | Adopts a CI-produced independent recheck record as `certificate/recheck.txt`. A contributor by hand; documented from `../../docs/development.md` |
| `certificate-freshness.sh` | Asserts a gate run left `certificate/` exactly as committed. `ci-macos-gate.yml`, `verify.yml` |
| `certificate-identity.sh` | Computes the content identity the generated certificate files name. `check.sh`, `ci-macos-recheck.yml` |
| `check-approvals.sh` | Verifies an approvals file is current. READ-ONLY. `check.sh`, `approve.sh` |
| `check-ci-docs-coherence.sh` | Verifies `docs/ci.md` and `.github/` agree (inventory, timeouts, `paths:`, SHA pins, cross-references), and that `.github/` holds no README shadowing the root one. READ-ONLY. `ci.yml` |
| `check-spdx.sh` | Verifies every hand-written source file carries its license header. READ-ONLY. `check.sh`, `ci.yml`, `verify.yml` |
| `comparator-configs.sh` | Derives `leanprover/comparator` configs from the registries and `policy.txt`. `ci-macos-recheck.yml`, and the recheck scripts below |
| `recheck-comparator.sh` | Runs Comparator on the example, in fresh clean rooms. `check.sh --recheck`, `ci-macos-recheck.yml` |
| `recheck-kernel.sh` | Replays the example's modules in Lean4Lean and leanchecker. `check.sh --recheck`, `ci-macos-recheck.yml` |
| `recheck-record.sh` | Renders the independent recheck's verdicts and writes `certificate/recheck.txt` (or `recheck.partial.txt`). `check.sh --recheck`, `ci-macos-recheck.yml` |
| `refresh-candidates.sh` | Regenerates `certificate/candidates.txt`, the Select candidate set. `check.sh` |
| `refresh-extraction.sh` | Regenerates the Charon/Aeneas extraction of the `framed_channel` crate. `check.sh`, `ci-macos.yml` |
| `refresh-hashes.sh` | Regenerates the statement-hash column of every registry. `check.sh` |
| `refresh-vectors.sh` | Regenerates `certificate/vectors.txt` by evaluating the Aeneas extraction. `check.sh` |
| `spec-check.sh` | Runs the Specify checker over the statement-only Challenge libraries. READ-ONLY. `check.sh`, `approve.sh` |

## `lib/`

Sourced only -- never executed directly.

| File | Role |
|---|---|
| `aeneas-revs.sh` | Revision coherence of the Charon/Aeneas extraction (`aeneas_rev_coherence`) |
| `approval-digests.sh` | What an approval record is bound to, shared by `approve.sh` and `check-approvals.sh` so the writer and the checker cannot disagree |
| `packages.sh` | The two Lake packages and the Lean-source helpers the scripts above share |
| `recheck-revs.sh` | Revision coherence of the independent recheck tools (`recheck_pin_coherence`, `recheck_rev_coherence`) |

## Navigation

- [Parent Directory](../README.md)
