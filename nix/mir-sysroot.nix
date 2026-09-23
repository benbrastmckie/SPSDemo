# mir-sysroot: an offline, host-target-only copy of AeneasVerif/charon's own
# nix/full-mir-sysroots.nix (fetched 2026-09-19 from
# https://github.com/AeneasVerif/charon/blob/main/nix/full-mir-sysroots.nix and reproduced here
# almost verbatim; credited, not invented). Upstream builds a "full MIR" sysroot for all 8
# targets its own rust-toolchain file lists (~780 MiB); this derivation restricts that recipe to
# `stdenv.hostPlatform.rust.rustcTarget` only -- the single target charon-driver needs to analyze
# this repository's own crate -- so the sysroot this flake ships is ~112 MB, not ~780 MiB.
#
# Why a Nix derivation instead of letting charon-driver build it at gate time: charon-driver
# (driver.rs, setup_miri_sysroot) falls back to `cargo miri setup --target=<target>
# --print-sysroot` under $CHARON_CACHE_DIR when no $CHARON_MIRI_SYSROOTS directory supplies the
# target. That still works (measured ~14 s cold, ~1.4 s warm) but writes outside the Nix store
# and is not reproducible or cacheable the way a derivation is; nix/aeneas-prebuilt.nix's wrapper
# sets CHARON_MIRI_SYSROOTS to this derivation's output so charon-driver never takes that path at
# gate time.
#
# CARGO_NET_OFFLINE=true plus rustNightly's own `rust-src` component (vendored under
# lib/rustlib/src/rust/library/vendor) as the crates-io replacement source: cargo never touches
# the network. rustNightly must carry the same "rust-src" and "miri" extensions
# nix/aeneas-prebuilt.nix requires for charon-driver itself (see nix/aeneas-pin.json's
# rust_components), or `cargo miri setup` fails for a missing component.
{
  runCommand,
  stdenv,
  rustNightly,
}:

let
  target = stdenv.hostPlatform.rust.rustcTarget;
in
runCommand "aeneas-mir-sysroot"
  {
    nativeBuildInputs = [ rustNightly ];
  }
  ''
    export HOME="$NIX_BUILD_TOP/home"
    export CARGO_HOME="$NIX_BUILD_TOP/cargo"
    export CARGO_NET_OFFLINE=true
    unset CHARON_ARGS CHARON_USING_CARGO RUSTC_WORKSPACE_WRAPPER RUSTC_WRAPPER
    mkdir -p "$HOME" "$CARGO_HOME"

    cat > "$CARGO_HOME/config.toml" <<END
    [source.crates-io]
    replace-with = "vendored-sources"
    [source.vendored-sources]
    directory = "$(rustc --print sysroot)/lib/rustlib/src/rust/library/vendor"
    END

    # Upstream loops over every toolchain-file target and relies on miri using the same
    # directory for every sysroot it sets up; restricted to one target, the loop collapses to a
    # single call.
    sysroot="$(cargo miri setup --target=${target} --print-sysroot)"

    mkdir -p "$out"
    cp -a "$sysroot/." "$out/"
  ''
