# .github/

> Deliberately named `CONTENTS.md`, not `README.md`: GitHub renders `.github/README.md` as the
> repository's front page in preference to the root `README.md`, so a README here silently
> replaces the project's own landing page. Do not rename this file back.

What GitHub Actions itself reads: twelve workflows, five composite actions they share, and
Dependabot's configuration. This is a directory map, not a second copy of what each workflow
does or certifies -- see [../docs/ci.md](../docs/ci.md) for the full trigger, job and
what-green-certifies detail this table only points at.

## Workflows

| Workflow | What it is | docs/ci.md |
|---|---|---|
| `ci.yml` | Linux build/test/lint, CI badge | [ci.yml](../docs/ci.md#ciyml-ci-badge) |
| `verify.yml` | The verification gate: certificate freshness plus the independent recheck, Verification badge | [verify.yml](../docs/ci.md#verifyyml-verification-badge) |
| `build-and-test.yml` | Reusable `workflow_call` job body `ci.yml`/`ci-macos.yml` invoke; not independently triggered | [build-and-test.yml](../docs/ci.md#build-and-testyml-shared-job-body) |
| `ci-windows.yml` | WSL2 validation of the documented Windows install path, on request | [Summary](../docs/ci.md#summary) |
| `ci-macos.yml` | Light macOS legs (build, prebuilt wiring, launcher compatibility), on request | [ci-macos.yml](../docs/ci.md#ci-macosyml-no-badge) |
| `ci-macos-gate.yml` | The full proof gate on aarch64-darwin, on request | [ci-macos-gate.yml and ci-macos-recheck.yml](../docs/ci.md#ci-macos-gateyml-and-ci-macos-recheckyml-no-badge) |
| `ci-macos-recheck.yml` | The macOS kernel replay, on request | same section |
| `setup-without-nix.yml` | Narrow, path-filtered coverage of the documented no-Nix procedure | [Summary](../docs/ci.md#summary) |
| `fresh-clone-canary.yml` | Monthly cold replay of the fresh-clone user path | [Summary](../docs/ci.md#summary), [Platform matrix](../docs/ci.md#platform-matrix) |
| `intel-installer-smoke.yml` | Under-two-minute check that the pinned Nix installer still works on Intel macOS | [Summary](../docs/ci.md#summary), [Timeouts](../docs/ci.md#timeouts) |
| `update-aeneas-pin.yml` | Weekly Aeneas pin-bump proposal | [Pin bump procedure](../docs/development.md#pin-bump-procedure) |
| `update-flake-inputs.yml` | Weekly nixpkgs/rust-overlay relock proposal | [Pin bump procedure](../docs/development.md#pin-bump-procedure) |

## Composite actions

| Action | Role |
|---|---|
| `actions/lean-toolchain/action.yml` (`verify.sh`) | Restore, verify, self-heal and save the elan-fetched Lean toolchain cache |
| `actions/mathlib-cache/action.yml` (`get.sh`) | Fetch Mathlib's oleans through `lake exe cache get`, with a from-source fallback on a miss |
| `actions/lake-bridge/action.yml` | Restore and save `framed_channel/{lean,aeneas}/.lake`, minus Mathlib's own build directory; see [docs/ci.md](../docs/ci.md#cache-strategy) |
| `actions/substituter-probe/action.yml` (`probe.sh`) | Classify every store path a resolved shell would realize, failing loudly on an unexpected from-source charon/aeneas build |
| `actions/precheck-incomplete/action.yml` (`run.sh`) | Run `check.sh` in a precheck mode (`--core-only`/`--committed-extraction`) and assert it exits exactly 3 (INCOMPLETE by design) |

See [docs/ci.md](../docs/ci.md#cache-strategy) for the caching rationale shared across every
caller.

## Other files

| File | Role |
|---|---|
| `dependabot.yml` | Weekly `github-actions`-ecosystem updates, grouped into one PR, labelled `dependencies`/`github-actions` |

## Navigation

- [Parent Directory](../README.md)
