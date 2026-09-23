# shellcheck shell=bash disable=SC2034
# SPDX-License-Identifier: Apache-2.0
# nix-version-floor.sh -- shared Nix version floor check. SOURCED, never executed.
#
# install.sh and full-gate.sh both refuse an unusably old `nix` with a clear, project-specific
# message rather than a confusing flakes/`nix develop` error later. Nix 2.4 is the floor: it is
# the release that shipped flakes and the `nix develop`/`nix build` CLI this repository's
# scripts use throughout (`nix flake metadata`, `nix build --dry-run`; `nix store
# prefetch-file`, used by the maintainer-only nix/bump-aeneas-pin.sh rather than by a launcher,
# is from the same flakes-CLI era). Checked against Nix's own release notes: no command any
# launcher or in-repo script calls needs anything newer than 2.4.
#
#   nix_version_string            prints the raw first line of `nix --version` (empty on
#                                  failure; never fails itself)
#   nix_version_floor_ok <raw> <floor>
#     True (exit 0) when the LAST `N.N[.N]` token in <raw> is >= <floor> (both "N.N" or
#     "N.N.N"). Taking the last such token reads both plain Nix ("nix (Nix) 2.24.9") and
#     Determinate Nix ("nix (Determinate Nix 3.3.2) 2.24.11", where the leading token is the
#     Determinate wrapper's own version, never Nix's) correctly: Nix's own version is always the
#     rightmost dotted-number token on the line.
#     Exit 2 (not 1) when <raw> carries no such token at all -- unparsable, not "too old" -- so
#     the caller can warn and continue instead of refusing a working install on a version string
#     this check does not recognise.
#
# Requires: bash >= 3.2, grep.

NIX_VERSION_FLOOR="2.4"

nix_version_string() {
  nix --version 2>/dev/null | head -n1
}

nix_version_floor_ok() {
  local raw="$1" floor="$2" ver v_maj v_min v_patch f_maj f_min f_patch
  ver="$(printf '%s\n' "$raw" | grep -oE '[0-9]+\.[0-9]+(\.[0-9]+)?' | tail -n1)"
  [ -z "$ver" ] && return 2
  IFS='.' read -r v_maj v_min v_patch <<< "$ver"
  IFS='.' read -r f_maj f_min f_patch <<< "$floor"
  v_patch="${v_patch:-0}"
  f_patch="${f_patch:-0}"
  if [ "$v_maj" -gt "$f_maj" ]; then return 0; fi
  if [ "$v_maj" -lt "$f_maj" ]; then return 1; fi
  if [ "$v_min" -gt "$f_min" ]; then return 0; fi
  if [ "$v_min" -lt "$f_min" ]; then return 1; fi
  [ "$v_patch" -ge "$f_patch" ]
}
