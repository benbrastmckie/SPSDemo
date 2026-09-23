# comparator: a real, pinned Nix derivation for leanprover/comparator, the trustworthy-checker
# binary for Lean proof submissions this repo's Comparator-based tooling relies on.
#
# Real derivation vs. loogle.nix-style silent-rebuild wrapper -- the decision, argued (this is
# the deliberate answer the task asked for, not a default):
#   1. Trust semantics: Comparator's entire purpose is to be the trustworthy party in an
#      adversarial check. A wrapper that clones `master` and silently rebuilds on first use (or
#      after a cache wipe) means the binary actually being trusted at verification time is
#      whatever `leanprover/comparator@master` happened to be on some unrecorded date, with no
#      Nix-store provenance and no way to reproduce or audit exactly what ran for a past verdict
#      -- a bad fit for a component whose green/red verdict downstream consumers rely on for a
#      Lean proof-verification trust boundary.
#   2. Tractability differs from loogle's case: loogle depends on Mathlib (thousands of files,
#      long first build) -- a real derivation there is a much heavier undertaking, which is why
#      the wrapper trade-off was reasonable for it. Comparator's dependency footprint is Lean
#      core + lean4export only (its own `lakefile.toml` has exactly one `[[require]]`, no
#      Mathlib) -- light enough that a pinned, offline-buildable derivation is realistic.
#   3. Neither `leanprover/comparator` nor `leanprover/lean4export` ships a `flake.nix`
#      (confirmed 404 on both via the GitHub API), so unlike loogle there is no upstream Nix
#      entry point to delegate version-resolution to even if we wanted to.
#
# Offline vendoring vs. FOD fallback: Comparator's own `[[require]]` for lean4export floats on
# `rev = "master"`. Rather than allowing network mid-build (a fixed-output derivation for the
# whole build, which trades away Nix's usual build-sandbox auditability), this derivation
# rewrites that require to a local `path`-style dependency pointing at a separately
# `fetchFromGitHub`-pinned lean4export source, entirely offline. This was verified in a scratch
# harness (network confirmed blocked via `unshare -rn`) before this file was written -- it works
# cleanly, so the FOD fallback documented as a contingency in the plan was NOT needed. Stating
# this explicitly per the "state the reasoning either way" instruction: no FOD fallback is used
# here.
#
# lean4export pin: the `lean4export_rev` field in ./comparator-pin.json is not a new pin invented
# here -- it is the exact commit Comparator's OWN stock `lake-manifest.json` already resolves
# `rev = "master"` to, as of the `comparator` commit pinned in that same file (v4.34.0 stable,
# bumped from the earlier v4.34.0-rc2 pin in lockstep with nix/lean-toolchain-bin.nix, which reads
# the pin file's `lean_toolchain_version`, and framed_channel/scripts/lib/recheck-revs.sh, which
# reads the same file at source time). This is Comparator's own lean4export dependency, used only
# for Comparator's own build/self-tests
# (fixed to Comparator's own toolchain) -- NOT the per-target-project resolver from
# packages/lean4export.nix, which solves a structurally different problem (matching an arbitrary
# target project's toolchain, not Comparator's own).
#
# nanoda: deliberately deferred (see packages/README.md) -- this derivation does not build or
# reference nanoda_bin.
{
  stdenv,
  fetchFromGitHub,
  lean-toolchain-bin,
  gitMinimal,
  autoPatchelfHook,
  gmp,
  libuv,
}:

let
  # Single source of truth: nix/comparator-pin.json (mirrors nix/aeneas-pin.json's shape).
  # framed_channel/scripts/lib/recheck-revs.sh reads the same file at source time (via
  # _recheck_load_pin), and nix/lean-toolchain-bin.nix reads its
  # lean_toolchain_version/lean_toolchain_assets fields -- both move automatically when this
  # file is bumped. recheck_tool_paths() matches the built binary's store path against the
  # short prefix of `.rev` (/nix/store/*-comparator-*-<rev8>*/*), and recheck_pin_coherence()
  # checks the one remaining hand-synced duplicate, the lean4export `rev` literal in
  # framed_channel/recheck/lakefile.toml, against this same file.
  comparatorPin = builtins.fromJSON (builtins.readFile ./comparator-pin.json);
  comparatorRev = comparatorPin.rev;
  lean4exportRev = comparatorPin.lean4export_rev;

  comparatorSrc = fetchFromGitHub {
    name = "comparator-src";
    owner = "leanprover";
    repo = "comparator";
    rev = comparatorRev;
    hash = comparatorPin.src_hash;
  };

  lean4exportSrc = fetchFromGitHub {
    name = "lean4export-src";
    owner = "leanprover";
    repo = "lean4export";
    rev = lean4exportRev;
    hash = comparatorPin.lean4export_src_hash;
  };
in
stdenv.mkDerivation {
  pname = "comparator";
  version = "0.1.0-${builtins.substring 0 8 comparatorRev}";

  # Two sibling source trees, assembled offline: Comparator's own lakefile.toml is patched (see
  # postPatch) to require lean4export via a local `path`, not `scope`/`rev`, so `lake build`
  # never needs network to resolve it.
  srcs = [
    comparatorSrc
    lean4exportSrc
  ];
  sourceRoot = ".";

  # comparatorSrc and lean4exportSrc unpack to their fetchFromGitHub-derived directory names
  # (comparator-<rev> / lean4export-<rev>); normalize to sibling `comparator/` and
  # `lean4export/` directories matching the `path = "../lean4export"` require below.
  postUnpack = ''
    mv comparator-* comparator
    mv lean4export-* lean4export
  '';

  # lean-toolchain-bin supplies bin/lean and bin/lake for the BUILD step only -- this is a
  # deliberate choice: at runtime, Comparator itself resolves `lean`/`lake`/`git` from whatever
  # is on the invoker's PATH (normally elan's per-project shims), exactly as its own README
  # assumes ("having an existing Lean installation ... present in PATH"). Hardcoding this
  # derivation's own pinned toolchain into a runtime wrapper would be actively wrong for callers
  # checking projects on a different Lean version -- lean-toolchain-bin exists to make *this*
  # derivation's *own* build reproducible, not to become Comparator's runtime toolchain.
  nativeBuildInputs = [
    lean-toolchain-bin
    gitMinimal
    autoPatchelfHook
  ];

  # The built `comparator` binary is a Lean-compiled ELF linked against the same shared
  # libraries Lean's own release binaries need (see lean-toolchain-bin.nix's identical
  # buildInputs); without these, `patchelf --print-interpreter` on the raw output names the
  # host's FHS-style dynamic linker (e.g. `/lib64/ld-linux-x86-64.so.2` on x86_64,
  # `/lib/ld-linux-aarch64.so.1` on aarch64), which resolves only via nix-ld on NixOS -- a
  # host-environment dependency this derivation should not carry. autoPatchelfHook rewrites the
  # interpreter/RPATH to their Nix store equivalents so the binary is self-contained, on every
  # platform it supports.
  buildInputs = [
    stdenv.cc.cc.lib
    gmp
    libuv
  ];

  postPatch = ''
    substituteInPlace comparator/lakefile.toml \
      --replace-fail '[[require]]
scope = "leanprover"
name = "lean4export"
rev = "master"' '[[require]]
name = "lean4export"
path = "../lean4export"'
    rm -f comparator/lake-manifest.json
  '';

  dontConfigure = true;

  buildPhase = ''
    runHook preBuild
    export HOME="$TMPDIR"
    cd comparator
    lake build lean4export comparator
    cd ..
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out/bin $out/share/comparator
    install -m755 comparator/.lake/build/bin/comparator $out/bin/comparator

    # Fixture tree and dev substitute script, shipped so verification (and downstream
    # consumers, e.g. sibling agent-system tooling depending on scripts/fake-landrun.sh) need no
    # second network fetch of Comparator's source tree.
    cp -r comparator/tests $out/share/comparator/tests
    cp -r comparator/scripts $out/share/comparator/scripts
    chmod +x $out/share/comparator/scripts/fake-landrun.sh

    runHook postInstall
  '';

  meta = {
    description = "Trustworthy Lean proof-verification checker (leanprover/comparator), pinned real derivation with vendored lean4export build dependency";
    homepage = "https://github.com/leanprover/comparator";
    platforms = [
      "x86_64-linux"
      "aarch64-linux"
    ];
  };
}
