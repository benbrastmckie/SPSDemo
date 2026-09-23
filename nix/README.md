# nix/

The derivations and pin files `../flake.nix` reads: the third-party build tooling this
repository's gate needs (Comparator, landrun, Charon/Aeneas), the scripts that keep each pin
current, and one offline Rust sysroot. No file here is the certified `framed_channel/` component
itself -- see [../docs/consuming.md](../docs/consuming.md) for what the flake does and does
not hand you.

| File | Role |
|---|---|
| `aeneas-pin.json` | Hand-maintained pin: Aeneas's `tag`/`rev`, the derived `charon_rev`, the `rust_nightly`/`rust_components` it was built with, and per-system release-asset hashes. Read by `aeneas-prebuilt.nix` and `bump-aeneas-pin.sh` |
| `aeneas-prebuilt.nix` | Fetches the pinned Aeneas release tarball and wraps the bundled `aeneas`/`charon`/`charon-driver` binaries to run reproducibly under Nix, with no source build |
| `bump-aeneas-pin.sh` | Implements the weekly pin-bump middle rule; see [docs/development.md](../docs/development.md#pin-bump-procedure) |
| `comparator.nix` | A real, pinned derivation for `leanprover/comparator`, vendored (not built from nixpkgs) |
| `comparator-pin.json` | Hand-maintained pin: Comparator's `rev`/`src_hash`, `lean4export_rev`/`lean4export_src_hash`, and the `lean_toolchain_version`/`lean_toolchain_assets` `lean-toolchain-bin.nix` builds against |
| `heavy-build-probe.sh` | Sourced (never executed) `nix build --dry-run` classifier: fails loudly on an unexpected from-source charon/aeneas build. Used by `.github/actions/substituter-probe` |
| `landrun.nix` | A pinned derivation for `landrun` v0.1.17, the Landlock-based sandbox Comparator's checks run inside |
| `lean-toolchain-bin.nix` | Deterministic acquisition of the exact Lean toolchain Comparator's own `lean-toolchain` pins, from `comparator-pin.json`'s `lean_toolchain_version`/`lean_toolchain_assets` |
| `lean-toolchain-pin.json` | Hand-maintained pin: the project's own Lean toolchain version and per-system release-asset sha256 digests elan fetches against |
| `lean-toolchain-pin.sh` | Checks (and can update) `lean-toolchain-pin.json` against the toolchain files and upstream's release API; see [docs/development.md](../docs/development.md#pin-bump-procedure)'s Manual-row procedure |
| `mir-sysroot.nix` | An offline, host-target-only MIR sysroot for the pinned Rust nightly (`cargo miri setup`, restricted from upstream Charon's all-target recipe), so Charon's extraction needs no network access |
| `nix-version-floor.sh` | Sourced (never executed) shared `nix` version floor check, used by `install.sh` and `full-gate.sh` |

## The five `packages.*` outputs

None of these is the certified component; each is third-party build tooling the gate depends on.

| Package | Systems | Consumed by |
|---|---|---|
| `comparator` | x86_64-linux, aarch64-linux (`hasComparator`) | The `.#recheck`/`.#full` dev shells; the local aarch64-linux comparator/lean-toolchain-bin smoke recipe (see [docs/development.md](../docs/development.md#pin-bump-procedure)); `verify.yml`'s `recheck` job resolves it through `.#recheck` |
| `lean-toolchain-bin` | x86_64-linux, aarch64-linux (`hasComparator`) | Comparator's own Lean toolchain, wherever `comparator` runs; the same smoke recipe checks its `lean --version` directly |
| `landrun` | Every Linux system (`pkgs.stdenv.isLinux`) | The `.#recheck`/`.#full` dev shells, as the sandbox Comparator's checks run inside |
| `charon-aeneas` | Wherever `aeneas-pin.json`'s `assets` object has an entry for the system (`hasAeneasPrebuilt`; currently x86_64-linux, aarch64-linux, aarch64-darwin) | The `.#extraction`/`.#full` dev shells (the bridge extraction's default route); `ci-macos.yml`'s `aeneas-prebuilt` job builds it directly as the darwin re-sign runtime check |
| `charon-aeneas-source` | Every system except x86_64-darwin (`hasAeneasSource`) | The `.#extraction-source` dev shell, the explicit last-resort from-source fallback in `full-gate.sh`'s fallback chain |

## Navigation

- [Parent Directory](../README.md)
