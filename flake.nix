{
  description = "Verification: pinned development shell for the framed_channel worked example";

  # No public substituter serves the pinned charon/aeneas source builds: the third-party cache
  # AeneasVerif/charon and AeneasVerif/aeneas CI used to push to stopped serving the pinned
  # outputs without any pin change on our side, and is not used here at all. cache.nixos.org is
  # the only substituter this flake or its consumers configure. charon/aeneas instead come from
  # upstream's own AeneasVerif/aeneas release tarball (nix/aeneas-prebuilt.nix), sha256-pinned by
  # nix/aeneas-pin.json, driven by the exact rust-overlay nightly the release names and an
  # offline host MIR sysroot (nix/mir-sysroot.nix). Never a Charon nightly release -- see
  # nix/aeneas-prebuilt.nix's header for why. The from-source route is kept as the explicit,
  # never-default `.#extraction-source` fallback (~30 min, ~12 GiB on a hosted runner); see
  # full-gate.sh's fallback chain (install.sh no longer warns about it: a plain `nix develop`
  # cannot build charon/aeneas from source at all since the shell split). Per-system asset
  # availability (which of x86_64-linux/aarch64-linux/aarch64-darwin the current pin serves a
  # prebuilt binary for): see nix/aeneas-pin.json, not this comment, so a pin bump never has to
  # edit prose here.
  #
  # framed_channel/certificate/digests.txt digests this file (as ../flake.nix, see
  # framed_channel/scripts/certificate-identity.sh's identity_digest_lines), so any edit here
  # changes the committed certificate's identity. After editing this file, regenerate the
  # certificate with `nix develop .#extraction --command bash framed_channel/check.sh` and commit the
  # resulting framed_channel/certificate/*.txt, or .github/workflows/verify.yml's
  # `Certificate freshness` step (git diff --exit-code -- framed_channel/certificate) will fail
  # on the next run. Verify locally first with `bash framed_channel/scripts/certificate-identity.sh
  # --check`.
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    # Deliberately NO `inputs.nixpkgs.follows` here: Aeneas pins the OCaml toolchain it needs, and
    # Charon pins its own Rust nightly, so following this flake's nixpkgs would break (or rebuild)
    # both. The locked revision in flake.lock must equal the `aeneas` rev in
    # framed_channel/aeneas/lake-manifest.json; framed_channel/scripts/lib/aeneas-revs.sh checks that.
    aeneas.url = "github:AeneasVerif/aeneas";
    # Supplies the exact-version Rust toolchain (rustc/cargo/rustfmt/clippy) plain nixpkgs cannot:
    # nixpkgs ships one rustc per channel, not one per point release. `rust-toolchain.toml` is the
    # single version source (see its own comment); this input follows this flake's own nixpkgs so
    # it never drags in a second, unrelated nixpkgs closure.
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    { nixpkgs, aeneas, rust-overlay, ... }:
    let
      # x86_64-darwin (Intel Mac) gets the shell without charon and aeneas: the Aeneas flake's
      # packages are built from its own nixos-unstable nixpkgs, which has dropped x86_64-darwin,
      # and pointing it at this flake's nixpkgs would break its pinned OCaml and Rust toolchains
      # (see the input comment above). Without those two only `check.sh --core-only` can run
      # there: the pre-check, which ends INCOMPLETE and never stands for the gate; a plain
      # check.sh fails at its preflight. nixpkgs 26.05 is the last release that
      # supports x86_64-darwin at all; drop the system and its CI leg together when nixpkgs
      # moves past 26.05.
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;

      # Seven purpose-named shells per system (not all present on every system -- see each
      # entry's own gate), each consumed by a specific CI job or local workflow so the coupling
      # stays visible when either side changes:
      #   lint             -- shellcheck, actionlint, git. Consumed by ci.yml's hygiene job.
      #   build            -- the pinned Rust toolchain, elan, jq, perl and git: everything
      #                       `check.sh --core-only` (the pre-check, not the gate) needs.
      #                       Consumed by ci.yml's build matrix.
      #                       No charon/aeneas/comparator/landrun.
      #   default          -- lint + build only, on every system. What a plain `nix develop`
      #                       gives a collaborator: enough to build and audit both packages
      #                       against the committed extraction (`check.sh --committed-extraction`)
      #                       without ever realizing charon, aeneas, comparator or landrun. This
      #                       used to be the union of every shell below; see `full`.
      #   full             -- the pre-split `default`: lint + build plus comparator
      #                       (`hasComparator`), the prebuilt charon/aeneas (`hasAeneasPrebuilt`)
      #                       and landrun (Linux). The opt-in "everything" shell for interactive
      #                       users; full-gate.sh never assigns it (its own `shell=` assignments
      #                       are `recheck`/`extraction`, `extraction-source` and `build`).
      #   extraction       -- build plus the prebuilt charon/aeneas, only where the pin carries a
      #                       release asset for this system (`hasAeneasPrebuilt`): the shell the
      #                       gate itself needs. Consumed by verify.yml's `verify` job (both the
      #                       x86_64-linux and aarch64-linux legs, via check.sh --aeneas).
      #   extraction-source -- build plus the `aeneas` flake input's own from-source
      #                       charon/aeneas packages (`hasAeneasSource`, i.e. every system except
      #                       x86_64-darwin): the explicit, never-default last-resort fallback
      #                       (~30 min, ~12 GiB). See full-gate.sh's fallback chain.
      #   recheck          -- build plus comparator (x86_64-linux and aarch64-linux), the pinned
      #                       landrun 0.1.17, and the prebuilt charon/aeneas where the pin carries
      #                       an asset (`hasAeneasPrebuilt`): every prerequisite
      #                       `check.sh --recheck` needs. Consumed by verify.yml's `recheck` job
      #                       (both legs; not a separately badged workflow of its own, distinct
      #                       from `verify`).
      # Lean itself is NOT provided by nix: elan installs the toolchain named in each package's
      # `lean-toolchain`, and Lake manages Lean dependencies -- this is unchanged by vendoring
      # Comparator below, whose own `lean-toolchain-bin` build input is scoped to Comparator's
      # own build only (see nix/comparator.nix's comment on that input) and never becomes a
      # second, nix-managed Lean toolchain on PATH.
      #
      # Comparator (the independent recheck's other `--recheck` tool, alongside landrun) IS now
      # provided, vendored under nix/ from ~/.dotfiles/packages/ and exposed as
      # `packages.comparator` -- x86_64-linux and aarch64-linux (`hasComparator` below), because
      # the derivation fetches a prebuilt Lean v4.34.0 (stable) release asset that upstream
      # publishes for those two platforms only (see nix/lean-toolchain-bin.nix's per-system asset
      # map). Its revision, Lean toolchain version and fetch hashes are single-sourced from
      # nix/comparator-pin.json, which nix/comparator.nix and nix/lean-toolchain-bin.nix both
      # read. The one duplicate that file cannot reach -- the lean4export `rev` literal in
      # framed_channel/recheck/lakefile.toml (Lake TOML has no external-file read) -- is checked
      # against the pin by framed_channel/scripts/lib/recheck-revs.sh's `recheck_pin_coherence`,
      # which also runs build-free in `check.sh`'s default path.
      # nix/comparator.nix's `autoPatchelfHook` makes the built binary self-contained
      # (Nix-store ELF interpreter and RPATH), so it does not depend on the host's nix-ld the way
      # `recheck/landrun-shim.sh`'s grant still does for elan's own `lake` binary on NixOS --
      # that grant is unrelated and unchanged; see its own comment.
      #
      # Computed once per system and shared between the `devShells` and `packages` outputs below
      # (each a projection of this attrset), so `pkgs` and the vendored nix/ derivations are each
      # evaluated/built exactly once per system rather than twice.
      perSystem = forAllSystems (
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ rust-overlay.overlays.default ];
          };
          rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
          # Aeneas/Charon: the pinned upstream release tarball (nix/aeneas-pin.json), never a
          # source build by default -- see the header comment above. `hasAeneasPrebuilt` reflects
          # whether the pin carries a release asset for this system (per-system, asset-aware; the
          # bump policy in nix/bump-aeneas-pin.sh keeps it asset-complete for every system it can).
          # `hasAeneasSource` gates the explicit last-resort fallback, `.#extraction-source`,
          # which builds `aeneas`'s own flake packages from source: available everywhere that
          # flake itself builds (not x86_64-darwin, whose nixpkgs has dropped the platform; see
          # the `systems` comment above), independent of whether a prebuilt asset exists.
          aeneasPin = builtins.fromJSON (builtins.readFile ./nix/aeneas-pin.json);
          hasAeneasPrebuilt = (aeneasPin.assets.${system} or null) != null;
          hasAeneasSource = system != "x86_64-darwin";
          # rust-overlay ships one manifest per nightly and fetches components from
          # static.rust-lang.org as fixed-output derivations -- no account, cache or token, the
          # same mechanism already serving rustToolchain (rust-toolchain.toml) below. `minimal` +
          # exactly the four extensions upstream's own `rust-toolchain` in the release tarball
          # names (never `fromRustupToolchainFile`, which would drag in all 8 of upstream's CI
          # target triples): nix/aeneas-prebuilt.nix asserts the tarball agrees at build time.
          rustNightly = pkgs.rust-bin.nightly.${aeneasPin.rust_nightly}.minimal.override {
            extensions = aeneasPin.rust_components;
          };
          mirSysroot = pkgs.callPackage ./nix/mir-sysroot.nix { inherit rustNightly; };
          aeneasPrebuilt = pkgs.callPackage ./nix/aeneas-prebuilt.nix {
            inherit rustNightly mirSysroot;
          };
          # comparator/lean-toolchain-bin are meaningful only where nix/lean-toolchain-bin.nix
          # pins a release asset (see its per-system map): x86_64-linux and aarch64-linux.
          hasComparator = builtins.elem system [
            "x86_64-linux"
            "aarch64-linux"
          ];
          # ci.yml's hygiene job expands `git ls-files '*.sh'` *inside* this shell for its
          # shellcheck step, so `git` is a genuine dependency of `lint` even though the shell
          # itself runs no git operation -- a deliberate departure from a bare
          # shellcheck+actionlint pair.
          lintPkgs = [
            pkgs.shellcheck
            pkgs.actionlint
            pkgs.git
          ];
          # Everything `check.sh --core-only` needs: the pinned Rust toolchain, elan (Lean
          # toolchain installer) and jq/perl/git (gate script tools).
          buildPkgs = [
            rustToolchain
            pkgs.elan
            pkgs.jq
            pkgs.perl
            pkgs.git
          ];
          # Vendored under nix/ from ~/.dotfiles/packages/ (see nix/*.nix header comments for the
          # full pin rationale). callPackage succeeds on every system -- nixpkgs itself is
          # universal -- but comparator and lean-toolchain-bin are meaningful only where
          # `hasComparator` holds (a fetched prebuilt Lean release asset, `meta.platforms` says
          # so), so only those systems expose them under `packages` below; `nix flake check
          # --all-systems` never tries to build them elsewhere. landrun 0.1.17 is portable Go and
          # is exposed on every Linux system.
          leanToolchainBin = pkgs.callPackage ./nix/lean-toolchain-bin.nix { };
          comparatorPkg = pkgs.callPackage ./nix/comparator.nix {
            lean-toolchain-bin = leanToolchainBin;
          };
          landrunVendored = pkgs.callPackage ./nix/landrun.nix { };
        in
        {
          devShells = {
            # Consumed by ci.yml's hygiene job (shellcheck, actionlint).
            lint = pkgs.mkShell { packages = lintPkgs; };

            # Consumed by ci.yml's build matrix. Deliberately no charon/aeneas: ci.yml runs
            # `check.sh --core-only`, the pre-check, which skips the extraction staleness and
            # bridge stages (reporting them, never passing them) and ends INCOMPLETE; a plain
            # check.sh (the gate) fails without those two binaries, so this shell is for the
            # pre-check only, not the verification claim.
            build = pkgs.mkShell { packages = buildPkgs; };

            # Consumed by verify.yml's `recheck` job (both legs; not a separately badged workflow
            # of its own, distinct from `verify`): build plus every prerequisite
            # `check.sh --recheck` needs -- comparator (`hasComparator`: x86_64-linux and
            # aarch64-linux), the pinned landrun 0.1.17 (Linux only), and the prebuilt
            # charon/aeneas where the pin carries an asset, since check.sh --recheck runs the
            # full gate (it refuses --core-only), not just the recheck tools alone.
            recheck = pkgs.mkShell {
              packages =
                buildPkgs
                ++ pkgs.lib.optionals hasComparator [ comparatorPkg ]
                ++ pkgs.lib.optionals pkgs.stdenv.isLinux [ landrunVendored ]
                ++ pkgs.lib.optionals hasAeneasPrebuilt [ aeneasPrebuilt ];
            };

            # A plain `nix develop` (every system): lint plus build only. No comparator,
            # charon/aeneas or landrun -- those are demanding (a real network fetch and/or a
            # prebuilt binary realization) and collaborators auditing proofs need none of them
            # (`check.sh --committed-extraction` runs here). Opt in with `.#full` below, or a
            # purpose-named shell (`extraction`, `extraction-source`, `recheck`) for exactly what
            # a given task needs.
            default = pkgs.mkShell { packages = lintPkgs ++ buildPkgs; };

            # The union of every shell above -- what `default` used to be before this split.
            # Kept for interactive users and CI/doc jobs that genuinely want everything at
            # once; see full-gate.sh, which drives this shell (or `extraction`/`extraction-source`
            # per its fallback chain) for the full Aeneas gate.
            full = pkgs.mkShell {
              packages =
                lintPkgs
                ++ buildPkgs
                ++ pkgs.lib.optionals hasComparator [ comparatorPkg ]
                ++ pkgs.lib.optionals hasAeneasPrebuilt [ aeneasPrebuilt ]
                ++ pkgs.lib.optionals pkgs.stdenv.isLinux [ landrunVendored ];
            };
          }
          // pkgs.lib.optionalAttrs hasAeneasPrebuilt {
            # Consumed by verify.yml's check.sh --aeneas job (the gate). Absent as an attribute
            # (not present-but-empty) wherever the pin carries no release asset for this system --
            # see `hasAeneasPrebuilt` above.
            extraction = pkgs.mkShell {
              packages = buildPkgs ++ [ aeneasPrebuilt ];
            };
          }
          // pkgs.lib.optionalAttrs hasAeneasSource {
            # Explicit last-resort fallback: builds the `aeneas` flake input's own charon/aeneas
            # packages from source (~30 min, ~12 GiB on a hosted runner) instead of fetching the
            # pinned release tarball. Never used by default; see full-gate.sh's fallback chain.
            # Absent (not present-but-empty) on x86_64-darwin -- see `hasAeneasSource` above.
            extraction-source = pkgs.mkShell {
              packages = buildPkgs ++ [
                aeneas.packages.${system}.charon
                aeneas.packages.${system}.aeneas
              ];
            };
          };

          # `hasComparator` systems only for comparator/lean-toolchain-bin (see the vendoring
          # comment above); landrun on every Linux system; charon-aeneas/charon-aeneas-source
          # wherever the corresponding hasAeneas{Prebuilt,Source} holds (see above).
          #
          # None of the attributes below is the certified `framed_channel/` component: they are
          # third-party build tooling this repository's own gate needs to run at all (Comparator,
          # landrun, and Charon/Aeneas). No output of this flake exposes the certified component
          # itself -- see docs/consuming.md for what this repository does and does not hand you.
          packages =
            pkgs.lib.optionalAttrs hasComparator {
              comparator = comparatorPkg;
              lean-toolchain-bin = leanToolchainBin;
            }
            // pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {
              landrun = landrunVendored;
            }
            // pkgs.lib.optionalAttrs hasAeneasPrebuilt {
              charon-aeneas = aeneasPrebuilt;
            }
            // pkgs.lib.optionalAttrs hasAeneasSource {
              charon-aeneas-source = pkgs.symlinkJoin {
                name = "charon-aeneas-source";
                paths = [
                  aeneas.packages.${system}.charon
                  aeneas.packages.${system}.aeneas
                ];
              };
            };
        }
      );
    in
    {
      devShells = builtins.mapAttrs (_: v: v.devShells) perSystem;
      packages = builtins.mapAttrs (_: v: v.packages) perSystem;
    };
}
