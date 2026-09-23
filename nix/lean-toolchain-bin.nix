# Deterministic, content-addressed acquisition of the exact Lean toolchain Comparator's own
# `lean-toolchain` pins (`leanprover/lean4:v4.34.0`, stable -- bumped from the v4.34.0-rc2
# release candidate in lockstep with nix/comparator.nix's `comparatorRev`/`lean4exportRev`; both
# this file and that one now read the single source of truth, ./comparator-pin.json, so a bump
# only has to edit that one file), for use as a build input by packages/comparator.nix. This
# does NOT build Lean 4 from source -- it fetches the official
# prebuilt Linux x86_64 release tarball for that exact tag as a fixed-output derivation (the
# only network-touching step) and unpacks it offline in a second, ordinary derivation.
#
# Route taken (of the two the research pass identified): (i) fetchurl of the GitHub Release
# tarball. `gh api repos/leanprover/lean4/releases/tags/v4.34.0` confirmed a
# `lean-4.34.0-linux.tar.zst` asset exists, so the elan-mediated fallback (route (ii)) was
# not needed. Per-system: the same release also publishes a `linux_aarch64` asset for
# aarch64-linux (`gh api` confirmed it and its digest cross-checked against `nix store
# prefetch-file`); x86_64-linux and aarch64-linux are the only platforms wired below, matching
# `meta.platforms` and flake.nix's `hasComparator`.
#
# flake.nix's `lean4` input (github:leanprover/lean4, unpinned rev, nixpkgs.follows) is
# deliberately NOT the source of this toolchain -- see the comment at that input in flake.nix.
# It floats on `leanprover/lean4`'s default branch and has no relationship to the exact
# `v4.34.0` tag Comparator's `lean-toolchain` pins; building Lean itself from that input
# would also mean building Lean 4 from source, which is unnecessary weight when upstream ships
# a release binary for the exact tag. It is left in flake.nix, unpinned, for a future consumer that
# wants Lean HEAD, with this file as the toolchain source of truth for Comparator specifically.
{
  stdenvNoCC,
  fetchurl,
  zstd,
  gnutar,
  autoPatchelfHook,
  gmp,
  libuv,
  stdenv,
}:

let
  # Single source of truth: nix/comparator-pin.json (see nix/comparator.nix's header comment).
  # `lean_toolchain_assets` holds one release asset per supported system: the upstream tarball
  # name and its digest, both verified against the v4.34.0 GitHub release (`gh api
  # repos/leanprover/lean4/releases/tags/v4.34.0`), cross-checked byte-for-byte against `nix
  # store prefetch-file`. A system outside this map throws a clear error rather than silently
  # evaluating an empty/wrong derivation.
  comparatorPin = builtins.fromJSON (builtins.readFile ./comparator-pin.json);
  version = comparatorPin.lean_toolchain_version;
  assets = comparatorPin.lean_toolchain_assets;
  asset =
    assets.${stdenvNoCC.hostPlatform.system} or (throw
      "lean-toolchain-bin.nix: no lean-${version} release asset is pinned for ${stdenvNoCC.hostPlatform.system} (only ${builtins.concatStringsSep ", " (builtins.attrNames assets)} are)"
    );

  # Fixed-output derivation: the only step in this file that touches the network.
  src = fetchurl {
    url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-${asset.asset}.tar.zst";
    hash = asset.hash;
  };
in
stdenvNoCC.mkDerivation {
  pname = "lean-toolchain-bin";
  inherit version src;

  nativeBuildInputs = [
    zstd
    gnutar
    autoPatchelfHook
  ];

  # Prebuilt upstream ELF binaries expect a standard FHS-ish dynamic linker layout;
  # autoPatchelfHook rewrites their interpreter/rpath to the Nix store equivalents.
  buildInputs = [
    stdenv.cc.cc.lib
    gmp
    libuv
  ];

  # No configure/build -- this is purely an unpack-and-relocate of prebuilt binaries. Offline:
  # only $src (already fetched by the FOD above) is touched.
  dontConfigure = true;
  dontBuild = true;

  unpackPhase = ''
    runHook preUnpack
    mkdir -p unpacked
    tar --zstd -xf "$src" -C unpacked
    runHook postUnpack
  '';

  installPhase = ''
    runHook preInstall
    # The release tarball extracts to a single top-level directory (lean-<version>-linux/)
    # containing bin/, lib/, include/, share/.
    srcdir="$(find unpacked -mindepth 1 -maxdepth 1 -type d | head -n1)"
    mkdir -p "$out"
    cp -r "$srcdir"/. "$out"/
    runHook postInstall
  '';

  # autoPatchelfHook runs its checks as part of the fixup phase automatically.

  meta = {
    description = "Prebuilt Lean 4 v${version} toolchain (lean, lake) fetched as a fixed-output derivation, for Comparator's own lakefile toolchain";
    homepage = "https://github.com/leanprover/lean4";
    platforms = [
      "x86_64-linux"
      "aarch64-linux"
    ];
  };
}
