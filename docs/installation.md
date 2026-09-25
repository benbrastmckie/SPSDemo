# Installation

The step-by-step version of the root [README.md](../README.md#install)'s Install section: what
each command needs, what it does, and what it deliberately does not do. For a machine without
Nix, see [setup-without-nix.md](setup-without-nix.md) instead.

## Prerequisites

- **A supported system**: x86_64-linux, aarch64-linux, aarch64-darwin or x86_64-darwin.
  `install.sh` refuses anything else before its first `nix` call. What each system can run
  differs -- see [ci.md#platform-matrix](ci.md#platform-matrix); on Windows, use WSL2 (see
  [setup-without-nix.md#windows](setup-without-nix.md#windows)).
- **git**.
- **bash 3.2 or later**, so the stock macOS `/bin/bash` works for `install.sh` and
  `full-gate.sh`. Everything else runs inside a Nix shell that brings its own bash.
- **[nix](https://nixos.org/download/) >= 2.4, with flakes enabled.** 2.4 is the release that
  shipped flakes and the `nix develop`/`nix build` CLI this repository's scripts use throughout;
  `install.sh` and `full-gate.sh` both check this floor (via `nix/nix-version-floor.sh`) before
  their first real `nix` call and refuse an older one with a clear message rather than a
  confusing flakes error later. The
  [Determinate Systems installer](https://determinate.systems/nix-installer/) enables flakes by
  default and always installs a current release, well above the floor:

  ```bash
  curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
  ```

  With any other installer, see
  [enabling flakes](https://wiki.nixos.org/wiki/Flakes#Enabling_flakes_permanently).
  `install.sh` never installs nix itself: when nix is missing it prints the command above and
  exits 2.

## Install

From the repository root:

```bash
bash install.sh
nix develop
```

`install.sh` checks the prerequisites above, activates a tracked pre-push hook
(`git config core.hooksPath .githooks`; see [development.md](development.md#pre-push-hook-checksh---core-only-before-every-push)
for what it runs and how to skip it for a deliberate WIP push -- skipped, with a notice, if
`core.hooksPath` is already set to something else, or if run outside a git work tree), then enters
the light build shell and warms its caches: it builds the Lean package (which makes elan download
the pinned Lean toolchain) and fetches the Rust crate's dependencies.
The script is idempotent and safe to re-run. It exits 0 when ready, 1 when a warm-up
step failed, and 2 on a usage error, an unsupported platform or a missing prerequisite.

| Flag | Effect |
|---|---|
| `--with-bridge` | also warm the Charon/Aeneas bridge package's Lean build: fetches Aeneas's Mathlib dependency (~7 GB on first fetch) after a `[y/N]` prompt, then builds it. Add it before a first full gate run to avoid paying that fetch there instead |
| `--yes` | accept the `--with-bridge` prompt non-interactively (a non-interactive session without it exits 2) |
| `--help` | the full usage text |

`nix develop` enters the **light shell**: the lint and build toolchains only (the pinned Rust
toolchain, elan, jq, perl, git, shellcheck, actionlint). Lean itself is not
provided by nix: elan installs the toolchain named in each package's `lean-toolchain` file, and
Lake manages the Lean dependencies.

## What the light shell does not include

A plain `nix develop` never realizes charon, aeneas, comparator or landrun, so entering it never
costs a from-source build, and no substituter, account or token is ever required for it:
`cache.nixos.org` is the only substituter this repository configures anywhere. Those tools are a
deliberate opt-in through `bash full-gate.sh`, which resolves the shell your system needs, reports
the real cost, and asks before anything demanding -- see
[development.md](development.md#running-the-full-gate-locally-opt-in).

The purpose-named dev shells, for when you want one directly (`nix develop .#<name>`):

| Shell | Contents |
|---|---|
| `default` | lint + build: what a plain `nix develop` gives you |
| `lint` | shellcheck, actionlint, git |
| `build` | the pinned Rust toolchain, elan, jq, perl, git |
| `extraction` | build plus the prebuilt charon/aeneas; present only where `nix/aeneas-pin.json` carries a release asset for the system |
| `extraction-source` | build plus charon/aeneas built from source (~30 min, ~12 GiB); absent on x86_64-darwin |
| `recheck` | build plus everything `check.sh --recheck` needs: comparator (Linux), landrun (Linux) and the prebuilt charon/aeneas |
| `full` | the union of the above |

[flake.nix](../flake.nix) is the authority for this table; each shell's comment there names the
CI job that consumes it. The other half of the same flake surface -- the five `packages.*`
outputs these shells wrap (`comparator`, `lean-toolchain-bin`, `landrun`, `charon-aeneas`,
`charon-aeneas-source`) -- is documented in [../nix/README.md](../nix/README.md).

## Upgrading from an earlier checkout

If an earlier version of this repository had you trust a `hacl.cachix.org` substituter (removed;
see [development.md#pinned-versions](development.md#pinned-versions)), you can optionally remove
its now-unused entry from `~/.local/share/nix/trusted-settings.json`.

## Next steps

- The root [README.md](../README.md#usage)'s Usage section for the basic commands.
- [development.md](development.md) for the development loop end to end, and its
  [Troubleshooting](development.md#troubleshooting) section when a step here fails.

## Navigation

- [docs/README.md](README.md)
- [Back to README](../README.md)
