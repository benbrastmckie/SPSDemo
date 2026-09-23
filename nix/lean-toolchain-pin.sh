#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# lean-toolchain-pin.sh -- did elan's release fetch land the exact bytes this repository pins?
#
# framed_channel's Lean toolchain (framed_channel/{lean,aeneas,recheck}/lean-toolchain, all three
# the same tag) is fetched by elan from a GitHub release tag with no hash verification of its
# own; the certificate only records the Lean commit after installation. This script closes that
# gap for a fresh download: nix/lean-toolchain-pin.json commits a per-system sha256 for the
# upstream release asset (the GitHub Releases API's own `digest: sha256:<hex>` field, stored
# lowercase hex rather than Nix's SRI form so it compares directly with that field -- JSON takes
# no comments, so this choice is recorded here instead), and this script checks a
# freshly-downloaded asset against it before elan installs it.
#
# This pins bytes, not the acquisition mechanism: elan itself still resolves and installs the
# toolchain from the same GitHub release tag it always has. This script is an independent, extra
# check that intercepts a fresh download beforehand -- run from full-gate.sh (when the pinned
# toolchain is not yet installed) and from .github/actions/lean-toolchain (on a cache miss). See
# docs/development.md's pin-bump procedure and docs/ci.md's cache-strategy note.
#
# Neither this script's own path nor nix/lean-toolchain-pin.json is a certificate-identity input
# (scripts/certificate-identity.sh's identity_file_list): the pin decides only how the toolchain
# is acquired, never a verdict. The three lean-toolchain files already are identity inputs, so a
# Lean bump changes the identity regardless of this script.
#
# Usage: bash nix/lean-toolchain-pin.sh [--check-consistency-only] [-h | --help]
#   (no option)                 full check: verify the pin and the lean-toolchain files agree,
#                                then download the pinned asset for this system and hash it
#   --check-consistency-only    only the offline, cheap pin/lean-toolchain-files agreement check;
#                                no network. Used when the toolchain is already installed.
#
# A system with no pinned asset (nix/lean-toolchain-pin.json's "assets" has no entry for it)
# prints a notice and exits 0 -- not a failure; the toolchain still installs, just unverified by
# this script.
#
# Test hooks (env vars; never set by a human -- see
# framed_channel/tests/lean-toolchain-pin/run.sh):
#   LEAN_TOOLCHAIN_PIN_TEST_PIN               pin file to read instead of
#                                              nix/lean-toolchain-pin.json
#   LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES   space-separated lean-toolchain files to check
#                                              consistency against, instead of the real three
#   LEAN_TOOLCHAIN_PIN_TEST_SYSTEM            system name to use instead of uname -s/-m
#   LEAN_TOOLCHAIN_PIN_TEST_FILE               a local file to hash instead of downloading
#
# Requires: bash >= 3.2 (runs under the host bash on macOS, like full-gate.sh), jq, curl (unless
# LEAN_TOOLCHAIN_PIN_TEST_FILE is set), coreutils (sha256sum) or shasum -a 256.
# Exit: 0 verified, consistent, or no pin for this system; 1 a digest mismatch or a
# pin/lean-toolchain inconsistency; 2 usage error or a missing required tool.

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

check_only=false
while [ "$#" -gt 0 ]; do
  case "$1" in
    --check-consistency-only) check_only=true; shift ;;
    -h|--help)
      awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "${BASH_SOURCE[0]}"
      exit 0 ;;
    *) echo "lean-toolchain-pin.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done

command -v jq > /dev/null 2>&1 || { echo "lean-toolchain-pin.sh: jq is required" >&2; exit 2; }

pin="${LEAN_TOOLCHAIN_PIN_TEST_PIN:-$ROOT/nix/lean-toolchain-pin.json}"
[ -f "$pin" ] || { echo "lean-toolchain-pin.sh: pin file not found: $pin" >&2; exit 2; }

pin_toolchain="$(jq -r '.lean_toolchain // empty' "$pin")"
if [ -z "$pin_toolchain" ]; then
  echo "lean-toolchain-pin.sh: $pin has no .lean_toolchain" >&2
  exit 2
fi

# Consistency: the pin's lean_toolchain must equal every framed_channel/*/lean-toolchain file
# (trimmed). A human bumping the Lean toolchain edits all three lean-toolchain files together
# (they are already a certificate-identity input); this check enforces that
# nix/lean-toolchain-pin.json is bumped in the same commit -- see docs/development.md's pin-bump
# procedure.
if [ -n "${LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES:-}" ]; then
  toolchain_files="$LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES"
else
  toolchain_files="$ROOT/framed_channel/lean/lean-toolchain $ROOT/framed_channel/aeneas/lean-toolchain $ROOT/framed_channel/recheck/lean-toolchain"
fi
want="$(printf '%s' "$pin_toolchain" | tr -d '[:space:]')"
inconsistent=""
for f in $toolchain_files; do
  if [ ! -f "$f" ]; then
    echo "lean-toolchain-pin.sh: lean-toolchain file not found: $f" >&2
    exit 2
  fi
  contents="$(tr -d '[:space:]' < "$f")"
  if [ "$contents" != "$want" ]; then
    inconsistent="$inconsistent $f"
  fi
done
if [ -n "$inconsistent" ]; then
  echo "lean-toolchain-pin.sh: $pin's lean_toolchain ($pin_toolchain) does not match:$inconsistent -- bump nix/lean-toolchain-pin.json in the same commit as the lean-toolchain files (see docs/development.md's pin-bump procedure)" >&2
  exit 1
fi

if $check_only; then
  echo "lean-toolchain-pin.sh: pin and lean-toolchain files agree ($pin_toolchain); --check-consistency-only, no network"
  exit 0
fi

# System detection, the same mapping full-gate.sh and install.sh use.
if [ -n "${LEAN_TOOLCHAIN_PIN_TEST_SYSTEM:-}" ]; then
  system="$LEAN_TOOLCHAIN_PIN_TEST_SYSTEM"
else
  case "$(uname -s)" in
    Linux) nix_os=linux ;;
    Darwin) nix_os=darwin ;;
    *) nix_os="" ;;
  esac
  case "$(uname -m)" in
    x86_64) nix_arch=x86_64 ;;
    aarch64|arm64) nix_arch=aarch64 ;;
    *) nix_arch="" ;;
  esac
  if [ -n "$nix_os" ] && [ -n "$nix_arch" ]; then
    system="${nix_arch}-${nix_os}"
  else
    system=""
  fi
fi

asset_name="$(jq -r --arg s "$system" '.assets[$s].name // empty' "$pin")"
asset_sha="$(jq -r --arg s "$system" '.assets[$s].sha256 // empty' "$pin")"
if [ -z "$asset_name" ] || [ -z "$asset_sha" ]; then
  echo "lean-toolchain-pin.sh: no pin for this system ($system); nothing to verify, elan will install unverified"
  exit 0
fi

sha256_of() {
  # sha256_of FILE -- lowercase hex, no filename
  if command -v sha256sum > /dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum > /dev/null 2>&1; then
    shasum -a 256 "$1" | cut -d' ' -f1
  else
    echo "lean-toolchain-pin.sh: neither sha256sum nor shasum is available" >&2
    exit 2
  fi
}

if [ -n "${LEAN_TOOLCHAIN_PIN_TEST_FILE:-}" ]; then
  actual="$(sha256_of "$LEAN_TOOLCHAIN_PIN_TEST_FILE")"
else
  command -v curl > /dev/null 2>&1 || { echo "lean-toolchain-pin.sh: curl is required" >&2; exit 2; }
  tag="${pin_toolchain#*:}"
  url="https://github.com/leanprover/lean4/releases/download/${tag}/${asset_name}"
  tmpdir="$(mktemp -d)"
  trap 'rm -rf "$tmpdir"' EXIT
  dest="$tmpdir/$asset_name"
  if ! curl --proto '=https' -fsSL -o "$dest" "$url"; then
    echo "lean-toolchain-pin.sh: failed to download $url" >&2
    exit 1
  fi
  actual="$(sha256_of "$dest")"
fi

if [ "$actual" = "$asset_sha" ]; then
  echo "lean-toolchain-pin.sh: verified $asset_name for $system (sha256:$actual)"
  exit 0
fi
echo "lean-toolchain-pin.sh: sha256 mismatch for $asset_name on $system: expected $asset_sha, got $actual" >&2
exit 1
