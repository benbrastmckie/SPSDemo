#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# verify.sh -- prove that ~/.elan holds a Lean toolchain that can actually run, and repair it once
# if it cannot. The verify step of the `lean-toolchain` composite action (action.yml, beside this
# file); runnable by hand from a checkout for the same diagnosis.
#
# Why this exists: elan's `lake`/`lean` are proxies that exec the installed toolchain's real
# binaries, and on Linux nixpkgs' elan patches every toolchain it installs so that its ELF
# interpreter and its `cc` wrapper are /nix/store paths of the nixpkgs revision that did the
# install. A ~/.elan produced under one nixpkgs revision is therefore dead under another whose
# store does not hold those paths, and every `lake` call fails with the opaque
#   error: command failed: 'lake' / No such file or directory (os error 2)
# The cache key carries the nixpkgs revision so that cannot be restored in the first place; this
# probe is the belt to that pair of braces, and it turns the symptom into a named diagnosis.
#
# Procedure: run `lake --version` and `lean --version` inside the named dev shell, in each of the
# three Lake packages (each has its own lean-toolchain file; a toolchain missing from ~/.elan is
# downloaded by this first call, which is also what populates a cold cache). On failure: emit a
# warning naming the cause, delete the installed toolchains, re-run the release-asset pin check
# (nix/lean-toolchain-pin.sh; the composite action's own pin-check step already ran once before
# this script, on the same cache miss that put this script on the fetch path in the first place,
# but the reinstall below is itself a second fetch and gets its own check), and probe exactly
# once more. A second probe failure is a hard error -- a retry must never mask a genuinely broken
# toolchain pin.
#
# Environment:
#   LEAN_TOOLCHAIN_SHELL   dev shell to probe in (default: build)
#   ELAN_HOME              elan's home (default: ~/.elan)
#   GITHUB_WORKSPACE       repository root (default: derived from this file's location)
#   GITHUB_OUTPUT          receives `verified=true|false` and `healed=true|false` (default: none)
#   GITHUB_STEP_SUMMARY    receives one result row (default: none)
#
# Usage: bash .github/actions/lean-toolchain/verify.sh [-h | --help]
# Requires: bash >= 3.2 (a macOS runner's `shell: bash` is /bin/bash 3.2; this file is in
# framed_channel/tests/launcher-compat/run.sh's scanned set), nix.
# Exit: 0 the toolchain runs (possibly after one repair), 1 it does not, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "verify.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

shell="${LEAN_TOOLCHAIN_SHELL:-build}"
root="${GITHUB_WORKSPACE:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)}"
elan_home="${ELAN_HOME:-$HOME/.elan}"
out="${GITHUB_OUTPUT:-/dev/null}"
summary="${GITHUB_STEP_SUMMARY:-/dev/null}"

probe() {
  # The inner script is single-quoted on purpose: it runs inside the dev shell, with the
  # repository root passed as $1.
  # shellcheck disable=SC2016
  nix develop "$root#$shell" --command bash -c '
    set -u
    for d in framed_channel/lean framed_channel/aeneas framed_channel/recheck; do
      [ -f "$1/$d/lean-toolchain" ] || continue
      echo "-- $d wants $(tr -d "[:space:]" < "$1/$d/lean-toolchain")"
      (cd "$1/$d" && lake --version && lean --version) || exit 1
    done
  ' probe "$root"
}

finish() {
  # finish VERIFIED HEALED
  echo "verified=$1" >> "$out"
  echo "healed=$2" >> "$out"
  echo "| Lean toolchain in \`.#$shell\` | verified: $1, healed: $2 |" >> "$summary"
}

echo "::group::lean-toolchain: probing lake and lean in .#$shell (ELAN_HOME=$elan_home)"
if probe; then
  echo "::endgroup::"
  finish true false
  exit 0
fi
echo "::endgroup::"

echo "::warning title=lean-toolchain self-heal::The Lean toolchain under $elan_home cannot run. On Linux the usual cause is a toolchain installed under a different nixpkgs revision: nixpkgs' elan patches each toolchain's ELF interpreter to a /nix/store path, which does not exist in this run's store ('No such file or directory (os error 2)'). Deleting the installed toolchains and reinstalling once. If this run RESTORED its ~/.elan from an exact cache key, that cache entry is bad: bump the epoch segment of the elan key in .github/actions/lean-toolchain/action.yml (see docs/ci.md)."
rm -rf "$elan_home/toolchains" "$elan_home/update-hashes"

# This reinstall is about to make elan fetch the toolchain again, exactly like a cache miss does
# -- re-run the release-asset pin check here too, so every download path this action can take is
# covered, not only the composite action's own cache-miss pin-check step (which already ran, and
# already passed, earlier in this same job; a failure here would mean the pinned asset changed
# out from under this run mid-flight, or the first check somehow did not run).
if ! bash "$root/nix/lean-toolchain-pin.sh"; then
  finish false true
  echo "::error title=lean-toolchain::the Lean toolchain release asset pin check failed before the self-heal reinstall; see above" >&2
  exit 1
fi

echo "::group::lean-toolchain: probing again after reinstalling"
if probe; then
  echo "::endgroup::"
  finish true true
  exit 0
fi
echo "::endgroup::"

finish false true
echo "::error title=lean-toolchain::lake/lean still cannot run in .#$shell after a clean reinstall of the toolchain. This is not a stale cache: check the lean-toolchain files, the elan package in the locked nixpkgs, and the network log of the download above."
exit 1
