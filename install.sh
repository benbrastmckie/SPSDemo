#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# install.sh -- check prerequisites and warm this repository's caches for first use.
#
# Verifies git and nix (with flakes) are on PATH, then enters the light `.#build` dev shell to
# pre-fetch what a first `check.sh --core-only` needs: the elan-managed Lean toolchains (via
# `lake build`) and the Rust crate's dependencies (`cargo fetch`). Idempotent: every warm-up
# command is itself a no-op on an already-warm tree, so re-running this script is always safe.
# Never realizes charon, aeneas, comparator or landrun -- a plain `nix develop` (`.#default`) is
# this same light shell; the full Aeneas gate is a deliberate opt-in (`bash full-gate.sh`, which
# resolves the right shell itself and asks before anything demanding), never something this
# script or a plain `nix develop` pays for silently.
#
# Never installs Nix. When nix is absent, this prints the Determinate Systems installer command
# and exits; run that yourself, then re-run this script.
#
# Also activates the tracked pre-push hook (.githooks/pre-push, which runs
# `check.sh --core-only` before every push -- see that file's own header): sets
# `git config core.hooksPath .githooks`, repository-local, when unset or already pointing there.
# When core.hooksPath is already set to something else, this script leaves it alone and prints
# the manual command instead of overwriting a contributor's own configuration. Skipped, with a
# notice, outside a git work tree (e.g. an extracted tarball copy). See docs/development.md's
# pre-push hook subsection for what it runs and how to skip it for a deliberate WIP push.
#
# Usage: bash install.sh [--with-bridge] [--yes] [-h | --help]
#   --with-bridge   also warm the Charon/Aeneas bridge package's Lean build (framed_channel/aeneas,
#                   inside the light `.#build` shell -- no charon/aeneas realized): fetches
#                   Aeneas's Mathlib dependency (~7 GB on first fetch), asking `[y/N]` first
#                   (`--yes` accepts; a non-TTY without `--yes` exits 2), then builds it. Omit this
#                   flag for a quick warm-up; add it before a first full Aeneas gate run to avoid
#                   paying the bridge fetch there instead.
#   --yes           accept the `--with-bridge` fetch prompt non-interactively.
#
# Requires: bash >= 3.2 (the stock macOS /bin/bash works); git; nix with flakes enabled (see
# https://wiki.nixos.org/wiki/Flakes#Enabling_flakes_permanently, or install via
# https://determinate.systems/nix-installer/, which enables flakes by default); one of
# flake.nix's four supported platforms (x86_64-linux, aarch64-linux, x86_64-darwin,
# aarch64-darwin).
# Exit: 0 ready, 1 a warm-up step failed, 2 usage error, an unsupported platform, or a
# missing/misconfigured prerequisite.

# Before anything else is parsed, so a pre-3.2 bash (or sh) gets a clear message.
if [ -z "${BASH_VERSION:-}" ]; then
  echo "install.sh: run with bash >= 3.2 (bash install.sh)" >&2
  exit 2
fi
case "$BASH_VERSION" in
  [0-2].*|3.[01].*)
    echo "install.sh: bash >= 3.2 is required (this is bash $BASH_VERSION)" >&2
    exit 2 ;;
esac

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

WITH_BRIDGE=0
YES=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    -h|--help)
      awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "${BASH_SOURCE[0]}"
      exit 0 ;;
    --with-bridge) WITH_BRIDGE=1; shift ;;
    --yes) YES=1; shift ;;
    *) echo "install.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done

# Map uname -s/-m to a Nix system string and gate on flake.nix's exact four-entry `systems`
# list (x86_64-linux, aarch64-linux, x86_64-darwin, aarch64-darwin), before the first `nix`
# invocation below. Anything else cannot succeed at any `nix develop` call.
case "$(uname -s)" in
  Linux) NIX_OS=linux ;;
  Darwin) NIX_OS=darwin ;;
  *) NIX_OS="" ;;
esac
case "$(uname -m)" in
  x86_64) NIX_ARCH=x86_64 ;;
  aarch64|arm64) NIX_ARCH=aarch64 ;;
  *) NIX_ARCH="" ;;
esac
if [ -n "$NIX_OS" ] && [ -n "$NIX_ARCH" ]; then
  system="${NIX_ARCH}-${NIX_OS}"
else
  system=""
fi
case "$system" in
  x86_64-linux|aarch64-linux|x86_64-darwin|aarch64-darwin) ;;
  *)
    echo "install.sh: unsupported platform '$(uname -s)/$(uname -m)'" >&2
    echo "Supported platforms: x86_64-linux, aarch64-linux, x86_64-darwin, aarch64-darwin." >&2
    case "$(uname -s)" in
      MINGW*|MSYS*|CYGWIN*)
        echo "Windows is not a flake.nix platform; use WSL2 and follow the Linux path from" >&2
        echo "there -- see docs/setup-without-nix.md#windows." >&2
        ;;
    esac
    exit 2 ;;
esac

echo "==> Checking prerequisites"

if ! command -v git > /dev/null 2>&1; then
  echo "install.sh: git is not on PATH; install it and re-run" >&2
  exit 2
fi

if ! command -v nix > /dev/null 2>&1; then
  echo "install.sh: nix is not on PATH. This script never installs Nix; run the Determinate" >&2
  echo "Systems installer yourself, then re-run install.sh:" >&2
  echo "  curl --proto '=https' --tls-v1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install" >&2
  echo "See https://determinate.systems/nix-installer/ (enables flakes by default)." >&2
  exit 2
fi

# shellcheck source=nix/nix-version-floor.sh
. "$ROOT/nix/nix-version-floor.sh"
nix_ver_raw="$(nix_version_string)"
if [ -n "$nix_ver_raw" ]; then
  nix_version_floor_ok "$nix_ver_raw" "$NIX_VERSION_FLOOR"
  nix_ver_rc=$?
  if [ "$nix_ver_rc" -eq 1 ]; then
    echo "install.sh: nix is older than this project's floor (needs >= $NIX_VERSION_FLOOR; found: $nix_ver_raw)." >&2
    echo "Flakes and 'nix develop'/'nix build' need at least Nix $NIX_VERSION_FLOOR. Upgrade via" >&2
    echo "  https://determinate.systems/nix-installer/ (or your package manager)." >&2
    exit 2
  elif [ "$nix_ver_rc" -eq 2 ]; then
    echo "install.sh: WARNING: could not parse a version number from 'nix --version' output ('$nix_ver_raw'); continuing without the floor check" >&2
  fi
else
  echo "install.sh: WARNING: 'nix --version' produced no output; continuing without the floor check" >&2
fi

flake_probe_out="$(nix flake metadata --no-write-lock-file "$ROOT" 2>&1 > /dev/null)"
flake_probe_status=$?
if [ "$flake_probe_status" -ne 0 ]; then
  if printf '%s\n' "$flake_probe_out" | grep -qi 'experimental Nix feature'; then
    echo "install.sh: flakes are not enabled. See" >&2
    echo "  https://wiki.nixos.org/wiki/Flakes#Enabling_flakes_permanently" >&2
    echo "or install via https://determinate.systems/nix-installer/, which enables them by default." >&2
  else
    echo "install.sh: 'nix flake metadata' failed for an unexpected reason:" >&2
    printf '%s\n' "$flake_probe_out" >&2
  fi
  exit 2
fi

echo "==> Prerequisites OK (git, nix with flakes)"

echo "==> Activating pre-push hook (git config core.hooksPath)"
if git -C "$ROOT" rev-parse --is-inside-work-tree > /dev/null 2>&1; then
  current_hooks_path="$(git -C "$ROOT" config --get core.hooksPath 2>/dev/null || true)"
  case "$current_hooks_path" in
    ""|.githooks)
      git -C "$ROOT" config core.hooksPath .githooks
      HOOK_STATUS="active (core.hooksPath=.githooks; runs check.sh --core-only before every push)"
      ;;
    *)
      echo "install.sh: core.hooksPath is already set to '$current_hooks_path'; leaving it alone." >&2
      echo "install.sh: to activate the --core-only pre-push hook too, run:" >&2
      echo "install.sh:   git config core.hooksPath .githooks" >&2
      HOOK_STATUS="NOT activated (core.hooksPath is already '$current_hooks_path')"
      ;;
  esac
else
  echo "install.sh: not inside a git work tree; skipping pre-push hook activation" >&2
  HOOK_STATUS="NOT activated (not a git work tree)"
fi

# name dir command -- runs `command` inside dir (relative to ROOT), under the `.#build` shell,
# with labeled output; exits 1 naming the step on failure.
warmup_step() {
  local name="$1" dir="$2" cmd="$3"
  echo "==> $name"
  if ! nix develop "$ROOT#build" --command bash -c "cd '$ROOT/$dir' && $cmd"; then
    echo "install.sh: warm-up step failed: $name" >&2
    exit 1
  fi
}

warmup_step "Lean toolchains + build (framed_channel/lean)" framed_channel/lean "lake build"
warmup_step "Rust dependency fetch (framed_channel/rust)" framed_channel/rust "cargo fetch"

if [ "$WITH_BRIDGE" -eq 1 ]; then
  echo "==> --with-bridge: fetching Aeneas/Mathlib cache (framed_channel/aeneas, ~7 GB on first fetch)"
  if [ "$YES" -ne 1 ]; then
    if [ ! -t 0 ]; then
      echo "install.sh: --with-bridge needs --yes in a non-interactive session (no TTY)" >&2
      exit 2
    fi
    printf 'Fetch Aeneas/Mathlib now (~7 GB on first fetch)? [y/N] ' >&2
    read -r reply
    case "$reply" in
      y|Y|yes|YES) ;;
      *) echo "install.sh: declined; skipping --with-bridge" >&2; exit 0 ;;
    esac
  fi
  attempt=1
  max_attempts=3
  fetched=0
  while [ "$attempt" -le "$max_attempts" ]; do
    if nix develop "$ROOT#build" --command bash -c "cd '$ROOT/framed_channel/aeneas' && lake exe cache get"; then
      fetched=1
      break
    fi
    echo "install.sh: lake exe cache get failed (attempt $attempt/$max_attempts)" >&2
    attempt=$((attempt + 1))
  done
  if [ "$fetched" -ne 1 ]; then
    echo "install.sh: warm-up step failed: Aeneas/Mathlib cache fetch (re-running install.sh --with-bridge is safe)" >&2
    exit 1
  fi
  echo "==> Building the bridge package (framed_channel/aeneas)"
  if ! nix develop "$ROOT#build" --command bash -c "cd '$ROOT/framed_channel/aeneas' && lake build"; then
    echo "install.sh: warm-up step failed: bridge package build" >&2
    exit 1
  fi
fi

cat <<EOM
==> Ready. Pre-push hook: $HOOK_STATUS
    Next:
  nix develop                                       # the light default shell (lint + build only)
  bash framed_channel/check.sh --committed-extraction   # build+audit both packages, no charon/aeneas
  bash full-gate.sh --dry-run                       # see what the full gate would cost on this machine
  bash full-gate.sh                                 # the verification gate (opt-in; asks before anything heavy)
EOM
