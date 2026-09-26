# Using this repository

This page answers the question the rest of `docs/` does not: what is actually here, what can you
run, and what should you not treat as fixed.

This repository is a worked example. It is used by **cloning it, reading the certificate, and
reproducing the gate** — not by taking a Nix or Lean dependency on the verified component. No
flake output exposes the certified `framed_channel/` component as an importable artifact;
`flake.nix` returns only `devShells` and `packages`, and every entry under `packages` is vendored
third-party build tooling the gate itself needs, not the thing the gate certifies.

That is the ordinary shape for a verification example. Proof developments in the Lean/Coq
ecosystem are conventionally cloned and built, then audited by reproducing the proof and its
certificate, rather than imported as packaged artifacts — the certificate is the thing that
travels. This repository follows that convention.

Nothing here is a stable interface. The example is free to move, and no part of it carries a
compatibility promise.

## What is here

The following is confirmed against the live tree, not transcribed once and left to drift; where a
detail (a flag list, a hash value) is likely to change, this page links to the command that
produces it instead of restating it.

### The three script CLIs

Three top-level scripts are the command-line surface, each self-documenting via `--help`:

- **`install.sh`** — checks prerequisites (git, nix with flakes) and warms this repository's
  caches (Lean toolchains, Rust crate dependencies) for first use.
  Never installs Nix itself and never realizes charon, aeneas, comparator or landrun. See
  `bash install.sh --help`.
- **`full-gate.sh`** — the opt-in launcher for the full verification gate: resolves which route
  the current machine takes (prebuilt extraction, from-source fallback, or a light audit-only
  fallback), probes and reports real cost before doing anything demanding, asks for consent, and
  then runs the gate. See `bash full-gate.sh --help`.
- **`framed_channel/check.sh`** — the verification gate itself: builds, audits, format-checks,
  lints and tests both Lean packages against the Rust extraction, and (with `--recheck`) drives
  the independent recheck. See `bash framed_channel/check.sh --help`.

### The flake surface

`flake.nix` exposes exactly two top-level outputs, both per-system: `devShells` and `packages`.
There is no `lib`, `overlays`, `templates`, or `checks` output.

- **`devShells`** — up to seven purpose-named shells per system, not all present on every system:
  `lint` (shellcheck, actionlint, git), `build` (the pinned Rust toolchain, elan, and the tools
  `check.sh --core-only` needs), `default` (`lint` + `build`; what a plain `nix develop` gives
  you), `full` (everything, opt-in), `extraction` and `extraction-source` (what the gate itself
  uses to realize charon/aeneas), and `recheck` (`build` plus the independent-recheck tooling).
  See `flake.nix`'s own per-shell comments for exactly which systems carry which shell.
- **`packages`** — per-system, up to five attribute names: `comparator` and `lean-toolchain-bin`
  (x86_64-linux and aarch64-linux only), `landrun` (Linux only), and `charon-aeneas` plus its
  from-source fallback `charon-aeneas-source` (wherever the corresponding route is available).
  **None of these is the certified component.** They are vendored third-party build tooling this
  repository's own gate needs to run at all; the same clarification is in `flake.nix` itself,
  next to the `packages` attrset.

### The certificate

`framed_channel/certificate/` holds one YAML manifest per certified unit, named for the unit
(`ring_buffer`, `vec_queue`, `varint`, `zigzag`, `crc8`, `stuff`, `seq_num`, `channel`,
`stuffed_channel`, `receiver`), a `shared.yaml` carrying the content every
manifest shares, generated whole-tree records written by every gate run (`digests.txt`,
`axioms.txt`, `ladder.txt`, `countermodels.txt`, and, under `--recheck`, `recheck.txt`), and
hand-maintained whole-tree records (`approvals.yaml`, `policy.txt`, `candidates.txt`). See
[framed_channel/certificate/README.md](../framed_channel/certificate/README.md) for the manifest
shape and what each ground class (`G0`-`G5`) means, and
[docs/trust-model.md](trust-model.md) for what a green result does and does not certify.

Every certified unit is bound to one content identity, a `sha256:<hex>` string computed over the
inputs a gate run touches (sources, build definitions, pins, policy, candidates and vectors).
Compute or check it yourself with
`bash framed_channel/scripts/certificate-identity.sh` (`--check` compares the tree's identity
against the committed records) — this page does not paste the current hash, since it changes on
every source edit.

## Ways to use it

Three are realistic. All three are audit paths: none of them hands you the certified component as
an importable dependency.

### Flake input

Adding this repository as a flake input gets you the dev shells and the three vendored tools
above — genuinely usable on their own — and nothing of the verified `framed_channel/` component
itself, since no output exposes it.

```nix
inputs.spsdemo.url = "github:benbrastmckie/SPSDemo";
```

```nix
# per-system access, e.g. inside your own flake's outputs
spsdemo.packages.${system}.comparator
spsdemo.devShells.${system}.default
```

### Copied

Copying `framed_channel/` into another tree is the only path that gets you the real Rust and Lean
sources rather than build tooling around them. But `framed_channel/check.sh` and its helper
scripts resolve their own paths relative to `framed_channel/` only, and are not parameterized by
a top-level project directory. A copy is therefore a fork you adapt, not a clean drop-in.

### Read

The example is meant to be read: [framed_channel/README.md](../framed_channel/README.md) walks
the six verification steps and points at the file or declaration implementing each one.

## What not to build against

None of the following is an interface. Each exists to serve the gate or the vendored packages
above, or is this repository's own tooling:

- **`framed_channel/scripts/*.sh` and `framed_channel/scripts/lib/*.sh`** — the gate's own helper
  scripts, invoked by `check.sh` and resolved relative to `framed_channel/`.
- **`nix/*.nix`** — the pin and vendoring files behind the flake's `packages` output (Aeneas,
  Comparator, landrun, the MIR sysroot); their shape follows what each vendored tool needs.
- **Every internal Lean module and declaration path** under `framed_channel/lean/` and
  `framed_channel/aeneas/` — these may move, and the certificate
  manifests (not the module paths) are the citable record of what was proved.

## Where to go next

- [docs/trust-model.md](trust-model.md) — what a green badge, a green gate run and a valid
  certificate actually certify, per platform.
- [docs/installation.md](installation.md) — step-by-step instructions for getting the gate
  running locally.
- [docs/ci.md](ci.md) — the workflows, the platform matrix, and what each badge covers.

## Navigation

- [Back to docs/](README.md)
- [Back to README](../README.md)
