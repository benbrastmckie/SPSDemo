# Setup without nix

The supported path is `nix develop` from the repository root; see
[installation.md](installation.md). This path stays supported alongside it (the decision below
records why), with narrow, path-filtered CI coverage:
[`setup-without-nix.yml`](../.github/workflows/setup-without-nix.yml) installs elan and confirms
the runner's own Rust toolchain, confirms the pinned Aeneas release asset below still resolves
upstream (an HTTP HEAD, no download), and runs `bash framed_channel/check.sh
--committed-extraction` with no Nix invocation at all. **What this covers**: the elan/Rust
install procedure below, and that the light audit against the committed extraction completes.
**What this does NOT cover**: no full gate, no Charon/Aeneas install or extraction replay, no
independent recheck -- see [docs/ci.md](ci.md#platform-matrix) for the full per-OS support
matrix and this job's exact scope.

**Why this path stays supported** (rather than marked unsupported): the tarball reference below
is already derived from the same `../nix/aeneas-pin.json` every other pinned reference in this
repository reads, so it self-updates on every Aeneas pin bump rather than needing separate
maintenance; keeping it covered by one small, path-filtered CI job costs less than the
maintenance debt of a document that ships unsupported and silently rots.

- [rustup](https://rustup.rs) -- `../rust-toolchain.toml` selects Rust 1.95.0.
- [elan](https://github.com/leanprover/elan) -- `../framed_channel/lean/lean-toolchain` selects
  the Lean version. elan's own fetch has no hash verification of its own; on this path (unlike
  `full-gate.sh`, which runs this automatically on a cache miss) that check is manual:
  `bash ../nix/lean-toolchain-pin.sh` checks the release asset elan just fetched against
  `../nix/lean-toolchain-pin.json`'s committed per-system sha256. It is not run automatically
  here because the automatic check lives in `full-gate.sh`, which this path does not use.
- `bash` >= 4.4, for `framed_channel/check.sh` and the scripts it runs -- macOS ships 3.2;
  install a newer bash separately and invoke the scripts with it. (The repository-root launchers
  `install.sh` and `full-gate.sh` do run under 3.2, but both drive Nix, so neither is part of
  this path.)
- GNU coreutils, `awk` and `perl` -- used by the gate and its scripts; coreutils provides
  `sha256sum`.
- `git` -- `framed_channel/scripts/check-spdx.sh` lists the files to check with it, and
  `framed_channel/scripts/check-approvals.sh` names the commit that recorded a stale approval.
- `jq` -- the staleness checks for the Charon/Aeneas extraction; `check.sh`'s preflight already
  refuses a missing `jq`, so this is enforced automatically, unlike `perl`.
- `curl` -- downloading the pinned Aeneas and Lean toolchain release tarballs below (a plain
  `curl -fsSL -o <file> <url>` works; any downloader that fetches the exact bytes does).
- [Charon and Aeneas](https://github.com/AeneasVerif/aeneas) -- the extraction and its bridge
  proofs, which the gate requires. Download the pinned release's tarball for your platform
  (`../nix/aeneas-pin.json`'s `tag` and `assets.<system>.name`, e.g.
  `https://github.com/AeneasVerif/aeneas/releases/download/<tag>/<asset name>`) and verify it
  against that same file's `assets.<system>.sha256` (an SRI `sha256-...` value; e.g.
  `sha256sum` the tarball, convert with `nix hash convert --to base16 sha256-...` if you have nix
  available just for that, or trust the release page's own published digest). Unpack it and put
  `aeneas`, `charon` and `charon-driver` on `PATH` (charon-driver additionally needs the exact
  Rust nightly the tarball's own `rust-toolchain` file names, with the `rustc-dev`/`llvm-tools`/
  `rust-src`/`miri` components -- `rustup toolchain install` from that file works). On **macOS**,
  keep the tarball's `libs/` directory next to the `aeneas` binary (it loads
  `@executable_path/libs/libgmp.10.dylib` from there). On **NixOS**, a prebuilt Linux binary like
  this one is linked against the standard `/lib64/ld-linux-x86-64.so.2` loader path, which NixOS
  does not provide by default; install and enable
  [`nix-ld`](https://github.com/nix-community/nix-ld) (or run the binaries through
  `nix develop` instead, which patches them via `autoPatchelfHook`). Without Charon/Aeneas, both
  `check.sh --core-only` (leaves the bridge out entirely) and `check.sh --committed-extraction`
  (audits the bridge against the committed extraction, needing only `jq` -- this is what
  [`setup-without-nix.yml`](../.github/workflows/setup-without-nix.yml) runs; see above) still
  run, and both end INCOMPLETE rather than standing for the gate.

`--recheck` always runs the full gate (Charon and Aeneas are required, same as a plain run), plus
one of two independent verdict producers per platform (see
[../framed_channel/recheck/README.md](../framed_channel/recheck/README.md) for the full detail):
the kernel replay (Lean4Lean, leanchecker) needs only `../framed_channel/recheck`'s tools built
(`lake build lean4lean/lean4lean lean4export/lean4export` from that directory) and the pinned
Lean toolchain, so it runs on macOS as on Linux -- elan installs the pinned
toolchain on demand, exactly as for the rest of the gate. (CI exercises the macOS replay with
elan supplied by the Nix shell, in `.github/workflows/ci-macos-recheck.yml`; the no-Nix macOS
combination uses the same elan-installed toolchain but is not separately exercised.) Comparator needs Linux's Landlock
sandbox, so **on macOS it is always reported `NOT-RUN`** (reason "Landlock sandbox is
Linux-only"); on Linux it additionally needs Comparator itself (built by hand from its own
README at the pinned revision, without Nix), landrun 0.1.17 or later, `strings` (binutils), a
working `systemd-run --user` and a non-root user.

Because Comparator's verdict is then `NOT-RUN`, a macOS `--recheck` run is never a *complete*
record: it is written to the gitignored `certificate/recheck.partial.txt`, not the committed
`certificate/recheck.txt` (see [docs/development.md](development.md#the-independent-recheck) for
the full record-completeness rule and how to adopt a complete, CI-produced record instead with
`framed_channel/scripts/adopt-recheck.sh`).

## Windows

Nix does not run natively on Windows. Use [WSL2](https://learn.microsoft.com/windows/wsl/install)
with a Linux distribution, install nix inside it, and follow the supported path from there; the
repository then behaves as on Linux. The recheck additionally needs systemd enabled in the
distribution (`systemd=true` in `/etc/wsl.conf`) and a kernel with Landlock;
`framed_channel/scripts/lib/recheck-revs.sh` probes both and reports NOT-RUN when either is
missing.

[`ci-windows.yml`](../.github/workflows/ci-windows.yml) is the dispatch-only leg that exercises
this path on a real `windows-2025` runner; see [docs/ci.md](ci.md#windows-runs-on-request-only)
for how to request a run. Its third dispatch (the first two hit an unrelated `curl` typo and a
CRLF-corrupted checkout, both fixed; see [docs/ci.md](ci.md#known-coverage-gaps)) ran this path
end to end and green, establishing it: WSL2 (Ubuntu-24.04, with `systemd=true`) provisions on the
runner, the Determinate installer installs Nix inside it, and `nix develop` realizes both the
`build` and `recheck` dev shells; `lake build`, `cargo test`, `check.sh --core-only` and all
fourteen fixture-runner steps pass; and the recheck prerequisites are
usable under WSL2 on this runner -- `recheck_systemd_user_usable`, `recheck_landlock_enforced`
and `recheck_landlock_abi` (ABI v7) all report the same result whether or not
`loginctl enable-linger` is run first, so linger makes no difference here.

**What is still genuinely open**, not resolved by this run: the checkout mounts as `v9fs`, not
DrvFs or ext4, though symlink and executable-bit round trips both work; the `$GITHUB_OUTPUT`,
`$GITHUB_ENV`, `$GITHUB_STEP_SUMMARY` and `$GITHUB_WORKSPACE` values GitHub Actions normally
provides are **not** reachable from inside the WSL2 shell on this runner, so a step that needs
them must write through the host shell instead (as `ci-windows.yml`'s own step-summary fallback
does); and CRLF normalization via this repository's root `.gitattributes` (`* text=auto eol=lf`)
is load-bearing for `nix develop` to work at all on a Windows checkout -- without it, `flake.nix`
checks out with CRLF line endings, which corrupts any shell script a derivation embeds literally
inside the file, breaking every `nix develop` invocation identically. The leg itself
stays `workflow_dispatch`-only and fully cold on every run (no `actions/cache`); the 28-minute
figure recorded for it in [docs/ci.md](ci.md#platform-matrix) predates the current, smaller
command set and is an upper bound.

## Navigation

- [Back to README](../README.md)
