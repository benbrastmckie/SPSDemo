# aeneas-prebuilt: fetches AeneasVerif/aeneas's own upstream release tarball for the pinned tag
# (nix/aeneas-pin.json) and wraps the bundled `aeneas`/`charon`/`charon-driver` binaries so they
# run reproducibly under Nix, with no source build and no third-party substituter.
#
# Why the Aeneas release, never a Charon nightly release: the Aeneas release's `charon-release`
# is built from Aeneas's own locked `charon-pin`, so the `charon`/`charon-driver` bundled here are
# expected to be the pinned commit -- and its Cargo-version-string LLBC compatibility check means a
# Charon nightly picked independently would frequently be the wrong version even when its commit
# differs from the Aeneas pin only by a few days. That expectation is upstream's release process,
# not something this derivation can enforce, so it is checked rather than assumed, twice:
# nix/bump-aeneas-pin.sh refuses at bump time any release whose bundled `charon version` differs
# from that revision's own `charon-pin` (recording the agreed value as `charon_rev` in the pin
# file), and framed_channel/scripts/lib/aeneas-revs.sh compares `charon version` on PATH with
# `charon_rev`, and `charon_rev` with the fetched sources' `charon-pin`, on every gate run.
#
# Binary shapes (measured against the actual pinned tarball, not assumed):
#   aeneas          fully static (pkgsStatic musl OCaml) -- needs no patching, no wrapper env.
#   charon          dynamic but only against glibc/libgcc_s -- resolved by autoPatchelfHook alone.
#   charon-driver   as charon, plus a NEEDED `librustc_driver-<hash>.so` (Linux) or bare
#                   `librustc_driver-<hash>.dylib`/`libLLVM.dylib` (darwin, no rpath) that only
#                   the pinned rust-overlay nightly (rustNightly, built with the same
#                   rustc-dev/llvm-tools extensions upstream's own `rust-toolchain` names)
#                   supplies; see nix/aeneas-pin.json's rust_nightly/rust_components.
#
# Runtime toolchain resolution: charon embeds its `rust-toolchain` at compile time and, with
# CHARON_TOOLCHAIN_IS_IN_PATH=1, runs charon-driver/cargo/rustc straight from PATH instead of
# shelling out to `rustup run <channel>` (upstream's own non-Nix path) -- the wrapper below
# prefixes PATH with rustNightly's bin/ so cargo and rustc resolve to that exact nightly.
# charon-driver's own MIR-sysroot lookup (CHARON_MIRI_SYSROOTS) is pointed at the offline
# mir-sysroot.nix derivation, so nothing is built into ~/.cache at gate time.
{
  lib,
  stdenv,
  fetchurl,
  makeWrapper,
  autoPatchelfHook,
  darwin,
  rustNightly,
  mirSysroot,
}:

let
  pin = builtins.fromJSON (builtins.readFile ./aeneas-pin.json);
  system = stdenv.hostPlatform.system;
  availableSystems = builtins.filter (s: pin.assets.${s} != null) (builtins.attrNames pin.assets);
  asset =
    pin.assets.${system} or (throw
      "aeneas-prebuilt.nix: no aeneas release asset is pinned for ${system} at tag ${pin.tag} (only ${builtins.concatStringsSep ", " availableSystems} are)"
    );

  # Fixed-output derivation: the only step in this file that touches the network. Hash verified
  # against the GitHub release API's own `digest` field for this asset (see nix/aeneas-pin.json).
  src = fetchurl {
    url = "https://github.com/AeneasVerif/aeneas/releases/download/${pin.tag}/${asset.name}";
    hash = asset.sha256;
  };

  # Short sha, for the installCheckPhase's `aeneas -version` comparison (the release binary
  # reports the tag, whose last `-`-separated segment is the short sha; upstream's tags use
  # git's 7-character abbreviation).
  shortRev = builtins.substring 0 7 pin.rev;
in
stdenv.mkDerivation {
  pname = "aeneas-prebuilt";
  version = "0-${shortRev}";
  inherit src;

  nativeBuildInputs = [
    makeWrapper
  ]
  ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ]
  ++ lib.optionals stdenv.hostPlatform.isDarwin [ darwin.autoSignDarwinBinariesHook ];

  # Linux: resolves charon-driver's NEEDED librustc_driver-*.so and libgcc_s via autoPatchelfHook.
  # aeneas is static and untouched by patchelf. darwin's dylib rewrite is done by hand in
  # postFixup below (install_name_tool), since autoPatchelfHook is Linux-only.
  buildInputs = lib.optionals stdenv.hostPlatform.isLinux [
    stdenv.cc.cc.lib
    rustNightly
  ];

  dontConfigure = true;
  dontBuild = true;

  unpackPhase = ''
    runHook preUnpack
    mkdir -p unpacked
    tar -xzf "$src" -C unpacked
    runHook postUnpack
  '';

  installPhase = ''
    runHook preInstall

    # Build-time fidelity assertion: the tarball's own rust-toolchain file must name the pinned
    # nightly, or a pin bump forgot to update rust_nightly/rust-overlay would silently pair the
    # wrong toolchain with these binaries.
    channel="$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' unpacked/rust-toolchain)"
    if [ "$channel" != "nightly-${pin.rust_nightly}" ]; then
      echo "aeneas-prebuilt.nix: tarball rust-toolchain channel '$channel' does not match the pinned nightly-${pin.rust_nightly}" >&2
      exit 1
    fi

    mkdir -p "$out/libexec/aeneas" "$out/bin"
    install -m755 unpacked/aeneas unpacked/charon unpacked/charon-driver "$out/libexec/aeneas/"
    # darwin's aeneas loads @executable_path/libs/libgmp.10.dylib (dylibbundler); harmless, and
    # required, on the systems that ship it.
    if [ -d unpacked/libs ]; then
      cp -r unpacked/libs "$out/libexec/aeneas/libs"
    fi

    makeWrapper "$out/libexec/aeneas/charon" "$out/bin/charon" \
      --set CHARON_TOOLCHAIN_IS_IN_PATH 1 \
      --set CHARON_MIRI_SYSROOTS ${mirSysroot} \
      --prefix PATH : ${rustNightly}/bin
    ln -s "$out/libexec/aeneas/aeneas" "$out/bin/aeneas"

    runHook postInstall
  '';

  # Rewrites charon-driver's bare librustc_driver-*.dylib/libLLVM.dylib references (upstream's own
  # charon-portable strips the rpath so `rustup run`'s DYLD_LIBRARY_PATH resolves them on the
  # non-Nix path) to the pinned rustNightly's store paths, then re-signs -- autoSignDarwinBinariesHook
  # runs automatically in fixupPhase for every Mach-O under $out once nativeBuildInputs carries it.
  postFixup = lib.optionalString stdenv.hostPlatform.isDarwin ''
    driver="$out/libexec/aeneas/charon-driver"
    for bare in $(otool -L "$driver" | awk 'NR>1 { print $1 }' | grep -E 'librustc_driver-|^libLLVM'); do
      name="$(basename "$bare")"
      target="${rustNightly}/lib/$name"
      if [ -f "$target" ]; then
        install_name_tool -change "$bare" "$target" "$driver"
      fi
    done
  '';

  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck

    charon_out="$("$out/bin/charon" version)"
    case "$charon_out" in
      *"${pin.charon_rev}"*) : ;;
      *)
        echo "aeneas-prebuilt.nix: charon version reported '$charon_out', expected it to contain ${pin.charon_rev}" >&2
        exit 1 ;;
    esac

    aeneas_out="$("$out/bin/aeneas" -version)"
    case "$aeneas_out" in
      *"${shortRev}") : ;;
      *)
        echo "aeneas-prebuilt.nix: aeneas -version reported '$aeneas_out', expected it to end in ${shortRev}" >&2
        exit 1 ;;
    esac

    if [ "${if stdenv.hostPlatform.isLinux then "1" else "0"}" = 1 ]; then
      if ldd "$out/libexec/aeneas/charon-driver" | grep -q 'not found'; then
        echo "aeneas-prebuilt.nix: charon-driver has an unresolved dynamic dependency:" >&2
        ldd "$out/libexec/aeneas/charon-driver" >&2
        exit 1
      fi
    else
      if otool -L "$out/libexec/aeneas/charon-driver" | grep -qi 'not found'; then
        echo "aeneas-prebuilt.nix: charon-driver has an unresolved dynamic dependency:" >&2
        otool -L "$out/libexec/aeneas/charon-driver" >&2
        exit 1
      fi
    fi

    runHook postInstallCheck
  '';

  passthru = {
    inherit (pin) tag rev;
  };

  meta = {
    description = "AeneasVerif/aeneas upstream release binaries (aeneas, charon, charon-driver), fetched as a fixed-output derivation and wrapped for Nix -- see nix/aeneas-pin.json for the pinned tag";
    homepage = "https://github.com/AeneasVerif/aeneas";
    platforms = availableSystems;
  };
}
