#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# get.sh -- fetch Mathlib's prebuilt oleans for the bridge package, with retries. The one step of
# the `mathlib-cache` composite action (action.yml, beside this file); runnable by hand from a
# checkout for the same result.
#
# Runs under the HOST bash (on a macOS runner that is /bin/bash 3.2, outside any Nix shell), so it
# is part of tests/launcher-compat's scanned set and must stay 3.2-compatible. The retry loop
# itself runs inside the dev shell, under Nix's bash.
#
# Environment:
#   MATHLIB_CACHE_SHELL     dev shell to run lake in (build, extraction, recheck); required
#   MATHLIB_CACHE_FALLBACK  what compiles Mathlib on a miss, for the warning text
#   GITHUB_OUTPUT           when set, receives `outcome=hit` or `outcome=miss`
#
# Usage: MATHLIB_CACHE_SHELL=build bash .github/actions/mathlib-cache/get.sh   (from the repo root)
# Requires: bash >= 3.2, nix.
# Exit: 0 hit, or miss after three network failures; 1 lake cannot execute; 2 usage error.

set -euo pipefail

shell_name="${MATHLIB_CACHE_SHELL:-}"
fallback="${MATHLIB_CACHE_FALLBACK:-the bridge build}"
out="${GITHUB_OUTPUT:-/dev/null}"

case "$shell_name" in
  build|extraction|recheck) ;;
  *) echo "get.sh: MATHLIB_CACHE_SHELL must be build, extraction or recheck (got '${shell_name}')" >&2; exit 2 ;;
esac

echo "::group::nix develop .#${shell_name} --command bash -c 'cd framed_channel/aeneas && lake exe cache get'"
rc=0
# The single-quoted body below is intentional: its `$` expansions must happen inside the nested
# `bash -c`, not in this outer script.
# shellcheck disable=SC2016
nix develop ".#${shell_name}" --command bash -c '
  set -euo pipefail
  # Enter the Lake package BEFORE the first lake call: elan picks the toolchain from the
  # lean-toolchain file of the working directory, the repository root has none, and a runner has
  # no default toolchain, so `lake` at the root fails with "no default toolchain configured"
  # however healthy ~/.elan is.
  cd framed_channel/aeneas
  # The lean-toolchain action already proved lake runs. If it cannot run HERE, that is not a
  # network failure and retrying cannot help: fail the job instead of spending three attempts and
  # then "compiling Mathlib from source" with a lake that is dead.
  if ! lake --version > /dev/null; then
    echo "::error::lake cannot execute in framed_channel/aeneas inside this shell (see the error above); this is a broken toolchain, not a Mathlib cache miss"
    exit 42
  fi
  for i in 1 2 3; do
    if lake exe cache get; then
      exit 0
    fi
    echo "lake exe cache get failed (attempt $i of 3)"
    sleep $((20 * i))
  done
  exit 1
' || rc=$?
if [ "$rc" -eq 0 ]; then
  echo "outcome=hit" >> "$out"
elif [ "$rc" -eq 42 ]; then
  echo "::endgroup::"
  exit 1
else
  echo "::warning::lake exe cache get failed 3 times; ${fallback} will compile Mathlib from source (correct, slower)"
  echo "outcome=miss" >> "$out"
fi
echo "::endgroup::"
