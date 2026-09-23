# Verified Components from Rust to Lean

**SPSDemo** — a secure program synthesis demo

[![CI](https://github.com/benbrastmckie/SPSDemo/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/benbrastmckie/SPSDemo/actions/workflows/ci.yml)
[![Verification](https://github.com/benbrastmckie/SPSDemo/actions/workflows/verify.yml/badge.svg?branch=main)](https://github.com/benbrastmckie/SPSDemo/actions/workflows/verify.yml)
[![Nix](https://img.shields.io/badge/built%20with-Nix-5277C3?logo=nixos&logoColor=white)](flake.nix)
[![Rust](https://img.shields.io/badge/Rust-1.95.0-orange)](rust-toolchain.toml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue)](LICENSE)
[![Lean](https://img.shields.io/badge/Lean-v4.31.0-blue)](framed_channel/lean/lean-toolchain)

This repository is the worked demonstration behind the talk "Verified Components from Rust to
Lean". It is one example, kept small enough to read end to end; it is not a library, and nothing
in it is a stable interface.

A small Rust crate (`framed_channel/rust`) is extracted to Lean by Charon/Aeneas, so the proofs
are about the code that actually runs rather than a hand-made copy of it. Hand-written Lean
specifications state what the code must do, and kernel-checked refinement theorems prove the
extraction meets them, by way of simpler intermediate models. The `check.sh` script is the gate
where a certificate records the result.

## Contents

```
.
├── flake.nix              pinned dev shells (light shell: lint + build; see docs/installation.md)
├── flake.lock             locked flake inputs (nixpkgs, rust-overlay, Aeneas)
├── rust-toolchain.toml    pins the Rust toolchain (1.95.0)
├── install.sh             checks prerequisites and warms the dev shell's caches
├── full-gate.sh           resolves your system's route and runs the verification gate
├── nix/                   vendored packages and pins (Aeneas, comparator, landrun, the MIR sysroot)
├── .github/workflows/     CI and Verification workflows
├── .github/actions/       composite actions shared across workflows (Lean toolchain, Mathlib cache)
├── docs/                  installation, development and CI documentation
├── framed_channel/        the example itself
│   ├── lean/              Lean specifications, models and theorems
│   ├── rust/              the Rust crate and its differential tests
│   ├── aeneas/            the Charon/Aeneas extraction and bridge proofs
│   ├── certificate/       registries, certificate manifests, approvals
│   ├── recheck/           independent recheck tools (kernel replay: any platform; Comparator: Linux)
│   ├── scripts/           refresh, approval, spec and recheck helper scripts
│   ├── tests/             fixture tests for the gate's tools; see tests/README.md
│   ├── approve.sh         records Select/Specify approvals into certificate/approvals.yaml
│   └── check.sh           the verification gate
├── CONTRIBUTING.md        the short contributor entry point
├── LICENSE                Apache License, Version 2.0
└── NOTICE                 third-party notices
```

- [framed_channel/README.md](framed_channel/README.md) - the example: five certified
  units, the extraction and its bridge proofs, registries, certificates and the recheck.
- [docs/consuming.md](docs/consuming.md) - what is here, what you can run, and what should not be
  treated as fixed.
- [docs/README.md](docs/README.md) - installation, development, CI and platform documentation.

## Install

Requires [nix](https://nixos.org/download/) with flakes enabled (the
[Determinate Systems installer](https://determinate.systems/nix-installer/) enables them by
default; otherwise see
[enabling flakes](https://wiki.nixos.org/wiki/Flakes#Enabling_flakes_permanently)). Without nix,
see [docs/setup-without-nix.md](docs/setup-without-nix.md).

```bash
# check prerequisites and warm the caches
bash install.sh

# enter the dev shell
nix develop
```

`install.sh` pre-fetches the Lean toolchain and the Rust dependencies, and
never installs nix itself; the dev shell holds the lint and build toolchains only. See
[docs/installation.md](docs/installation.md) for step-by-step instructions, the `install.sh`
flags and every dev shell.

## Usage

```bash
# fast audit against the committed extraction (inside nix develop)
bash framed_channel/check.sh --committed-extraction

# dry run: report the gate's route and cost
bash full-gate.sh --dry-run

# the full verification gate (first run fetches ~7 GB)
bash full-gate.sh --yes

# the gate plus the independent recheck
bash full-gate.sh --recheck --yes
```

The audit ends `INCOMPLETE` (exit 3) by design and is never the verification claim; exit 0 from
`full-gate.sh` is. `full-gate.sh` enters the shell it needs itself, `--yes` answers its consent
prompts. The full gate reproduces from hash-locked inputs on x86_64-linux, aarch64-linux and
aarch64-darwin, and each of the three asserts a byte-identical certificate in CI (strict on
x86_64-linux; apart from the target triple, via `--portable-host`, on the other two). The
complete independent recheck runs on Linux only; x86_64-darwin is a light audit, not a
verification, under its standing sunset decision (no new OS or architecture is planned beyond
these four platforms). See [docs/ci.md#platform-matrix](docs/ci.md#platform-matrix) for what each
system can run. See [docs/trust-model.md](docs/trust-model.md) for what a green badge, a green
gate run and a valid certificate do and do not certify, per platform.
`install.sh` and `full-gate.sh` run under the host's own `bash` before any dev shell exists, so
that bash must be `>= 4.4` (every other command above runs inside the dev shell, whose `bash` is
already pinned newer).

See [docs/development.md](docs/development.md) for the full development loop (routes and flags,
approvals, certificate regeneration, adopting the CI-produced recheck record, troubleshooting),
and [framed_channel/tests/README.md](framed_channel/tests/README.md) for the fixture tests.
`install.sh`, `full-gate.sh` and `check.sh` each accept `--help`.

## License

Apache License, Version 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
