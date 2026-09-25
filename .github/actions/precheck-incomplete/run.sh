#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# run.sh -- the one step of the `precheck-incomplete` composite action (action.yml, beside this
# file); runnable by hand from a checkout for the same diagnosis. Kept as its own file, not an
# inline `run:` block, so shellcheck can see it (the substituter-probe/mathlib-cache precedent).
#
# Runs under the HOST bash (a macOS runner's default `run:` shell is /bin/bash 3.2, outside any
# Nix shell, for fresh-clone-canary.yml's darwin legs -- see this action's own header for why
# ci-windows.yml is NOT a caller), so it stays 3.2-compatible: no bash 4+ features (associative
# arrays, `${var,,}`, mapfile, etc). Assumes the working directory is the checked-out repository
# root, exactly as every caller's original hand-written step already did.
#
# Environment (set by action.yml from its inputs):
#   PRECHECK_MODE        core-only | committed-extraction (required)
#   PRECHECK_SHELL_ATTR  dev shell attribute for `nix develop .#<attr>` (default: empty = plain
#                        `nix develop`, no attribute)
#   PRECHECK_USE_NIX     "true" (default) wraps the check in `nix develop ... --command`; "false"
#                        runs check.sh directly with plain bash (the no-Nix leg)
#
# Exit: 0 the precheck ended INCOMPLETE (exit 3, by design), 1 any other exit code, 2 usage error
# (an unrecognized PRECHECK_MODE).

set -u

case "${PRECHECK_MODE:-}" in
  core-only|committed-extraction) ;;
  *)
    echo "::error::precheck-incomplete: PRECHECK_MODE must be 'core-only' or 'committed-extraction' (got '${PRECHECK_MODE:-}')" >&2
    exit 2
    ;;
esac

# Same fallback every ci-windows.yml nix-calling step already repeats for its own (unrelated)
# WSL2 PATH reset -- harmless no-op here, on every caller of this action, since none of them are
# ci-windows.yml (see this action's own header) and nix is already on PATH via
# DeterminateSystems/nix-installer-action.
if ! command -v nix > /dev/null 2>&1; then
  # shellcheck disable=SC1091
  . /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh 2>/dev/null || true
fi

use_nix="${PRECHECK_USE_NIX:-true}"
shell_attr="${PRECHECK_SHELL_ATTR:-}"

if [ "$use_nix" = false ]; then
  cmd_desc="bash framed_channel/check.sh --${PRECHECK_MODE}"
elif [ -n "$shell_attr" ]; then
  cmd_desc="nix develop .#${shell_attr} --command bash framed_channel/check.sh --${PRECHECK_MODE}"
else
  cmd_desc="nix develop --command bash framed_channel/check.sh --${PRECHECK_MODE}"
fi

echo "::group::$cmd_desc"
rc=0
if [ "$use_nix" = false ]; then
  bash framed_channel/check.sh "--${PRECHECK_MODE}" || rc=$?
elif [ -n "$shell_attr" ]; then
  nix develop ".#${shell_attr}" --command bash framed_channel/check.sh "--${PRECHECK_MODE}" || rc=$?
else
  nix develop --command bash framed_channel/check.sh "--${PRECHECK_MODE}" || rc=$?
fi

if [ "$rc" -ne 3 ]; then
  if [ "$PRECHECK_MODE" = core-only ]; then
    echo "::error::check.sh --core-only exited $rc; the pre-check ends INCOMPLETE (exit 3) by design, and an exit 0 here would mean check.sh claimed PASS without the bridge"
  else
    echo "::error::check.sh --committed-extraction exited $rc; it ends INCOMPLETE (exit 3) by design, and any other exit code is a defect"
  fi
  exit 1
fi
echo "::endgroup::"
