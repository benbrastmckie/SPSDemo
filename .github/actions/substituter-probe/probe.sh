#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# probe.sh -- the one step of the `substituter-probe` composite action (action.yml, beside this
# file); runnable by hand from a checkout for the same diagnosis. Kept as its own file, not an
# inline `run:` block, so shellcheck can see it (the mathlib-cache/get.sh precedent).
#
# Runs under the HOST bash (a macOS runner's default `run:` shell is /bin/bash 3.2, outside any
# Nix shell, for fresh-clone-canary.yml's darwin legs), so it stays 3.2-compatible: no bash 4+
# features (associative arrays, `${var,,}`, etc).
#
# Environment:
#   PROBE_SHELL_ATTR  flake devShell attribute to probe (e.g. devShells.x86_64-linux.extraction);
#                      required
#   PROBE_CONTEXT      optional clause appended to messages (e.g. "on a fresh, cold clone");
#                      default: empty
#   GITHUB_WORKSPACE   repository root (default: derived from this file's location)
#
# Exit: 0 the probe ran and no from-source charon/aeneas build would happen; 1 otherwise (the
# probe itself failed, or a from-source build would happen).

set -euo pipefail

root="${GITHUB_WORKSPACE:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)}"
# shellcheck source=../../../nix/heavy-build-probe.sh
. "$root/nix/heavy-build-probe.sh"

if [ -z "${PROBE_SHELL_ATTR:-}" ]; then
  echo "probe.sh: PROBE_SHELL_ATTR is required" >&2
  exit 2
fi

ctx=""
[ -n "${PROBE_CONTEXT:-}" ] && ctx=" ${PROBE_CONTEXT}"

if ! heavy_probe "$root" "$PROBE_SHELL_ATTR"; then
  echo "::error::the substituter probe itself failed (nix build --dry-run); see the log above"
  exit 1
fi
if [ -n "$PROBE_SOURCE" ] || [ "$PROBE_OK" != true ]; then
  echo "::error::charon or aeneas would be built from source${ctx}: no configured substituter serves the pinned charon/aeneas. Offending store paths: $(tr '\n' ' ' <<< "$PROBE_SOURCE")"
  exit 1
fi
[ -n "$PROBE_PREBUILT" ] && echo "::notice::prebuilt-route/comparator/landrun/lean-toolchain-bin local build(s) (seconds to minutes, expected${ctx}): $(tr '\n' ' ' <<< "$PROBE_PREBUILT")"
[ -n "$PROBE_MINOR" ] && echo "::notice::Comparator/landrun local build(s) (minutes, not hours, expected${ctx}): $(tr '\n' ' ' <<< "$PROBE_MINOR")"
[ -n "$PROBE_FETCH_LINE" ] && echo "::notice::$PROBE_FETCH_LINE"
echo "substituters serve charon and aeneas${ctx} (nothing but the shell environment, and the prebuilt route's own fast local builds, would be built)"
