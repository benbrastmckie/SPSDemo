# shellcheck shell=bash disable=SC2034
# SPDX-License-Identifier: Apache-2.0
# heavy-build-probe.sh -- shared `nix build --dry-run` classifier. SOURCED, never executed.
# The PROBE_* variables are for the caller that sources this file (hence SC2034 off).
#
# full-gate.sh and the `substituter-probe` composite action (.github/actions/substituter-probe,
# used by verify.yml's four legs and fresh-clone-canary.yml) both need the same answer to "would
# realizing this installable build charon or aeneas from source" -- a from-source build is the one
# genuinely expensive case (~30 min, ~12 GiB) this repository never runs by default. Rather than
# each maintaining its own regex against `nix build --dry-run` output, both source this file and
# call `heavy_probe`.
#
#   heavy_probe <flake-ref> <installable>
#     Runs `nix build --dry-run <flake-ref>#<installable>` and sets:
#       PROBE_SOURCE      newline-separated to-be-built store paths whose name is a from-source
#                         charon/aeneas package name (see PROBE_SOURCE_NAME_RE below); empty when
#                         nothing from-source would be built.
#       PROBE_PREBUILT    to-be-built store paths belonging to the prebuilt Aeneas route itself
#                         (aeneas-prebuilt-*, aeneas-mir-sysroot, mir-sysroot*) or to a
#                         from-source Comparator/landrun component: real local work, but never
#                         "hours" -- informational, never an error. Includes every PROBE_MINOR path.
#       PROBE_MINOR       the subset of PROBE_PREBUILT that is Comparator/landrun/lean-toolchain-bin
#                         (kept separate so a caller can print a shorter, distinct notice for it).
#       PROBE_FETCH_LINE  the dry-run's own "these N paths will be fetched (X MiB download, Y MiB
#                         unpacked)" header line, verbatim, or empty when nothing would be fetched.
#       PROBE_REALIZED    "true" when the dry-run reports anything at all to build or fetch,
#                         "false" when the installable is already fully realized.
#       PROBE_OK          "true" unless PROBE_SOURCE is non-empty.
#     Returns non-zero (and prints the dry-run log to stderr) only when `nix build --dry-run`
#     itself fails (e.g. a bad installable) -- never merely because PROBE_SOURCE is non-empty; the
#     caller decides what a non-empty PROBE_SOURCE means (full-gate.sh's fallback chain, or
#     verify.yml's ::error::).
#
#   pin_has_asset <system> [<pin-file>]
#     True (exit 0) when nix/aeneas-pin.json (or <pin-file>) names a release asset for <system>.
#
#   pin_source_known_broken <system> [<pin-file>]
#     True (exit 0) when the pin's source_build_known_broken names <system>.
#
# Derivation-name patterns below were confirmed by `nix derivation show -r` of
# `.#devShells.x86_64-linux.{extraction,extraction-source}` at the nightly-2026.09.17-86158eb pin:
#   extraction-source's from-source closure names: charon, charon-<ver>, charon-deps-<ver>,
#     charon-full-mir-sysroots, ocaml<ver>-charon-<ver>, ocaml<ver>-aeneas-<ver>, and the
#     charon-aeneas-source symlinkJoin itself (also named "charon-aeneas-source", so it matches
#     the same "^charon" pattern -- correctly, since building it does mean building from source).
#   extraction's own closure never contains any of the above: its two local builds are named
#     aeneas-prebuilt-<tag>-<sha> and aeneas-mir-sysroot, neither of which ends in a bare
#     version-number suffix after "-charon"/"-aeneas", which is exactly what distinguishes them.
#
# Requires: bash >= 3.2 (full-gate.sh sources this under the host bash, which on macOS is 3.2;
# framed_channel/tests/launcher-compat/run.sh enforces it), nix, awk, grep, jq (only for
# pin_has_asset/pin_source_known_broken).

PROBE_SOURCE_NAME_RE='^charon(-.*)?$|^ocaml[0-9][0-9.]*-(charon|aeneas)-.*$'
PROBE_PREBUILT_NAME_RE='^aeneas-prebuilt(-.*)?$|^aeneas-mir-sysroot$|^mir-sysroot(-.*)?$'
PROBE_MINOR_NAME_RE='^comparator(-.*)?$|^landrun(-.*)?$|^lean-toolchain-bin(-.*)?$'

heavy_probe() {
  local flake_ref="$1" installable="$2" log built fetch_line path name
  log="$(mktemp)"
  if ! nix build --dry-run "${flake_ref}#${installable}" > "$log" 2>&1; then
    echo "heavy_probe: nix build --dry-run ${flake_ref}#${installable} failed" >&2
    cat "$log" >&2
    rm -f "$log"
    return 2
  fi
  PROBE_SOURCE=""
  PROBE_PREBUILT=""
  PROBE_MINOR=""
  PROBE_FETCH_LINE=""
  PROBE_REALIZED=false
  built="$(awk '
    /^this derivation will be built:$/ { p = 1; next }
    /^these [0-9]+ derivations will be built:$/ { p = 1; next }
    /^these [0-9]+ paths will be fetched/ { p = 0 }
    p { sub(/^[[:space:]]+/, ""); print }
  ' "$log")"
  fetch_line="$(grep -E '^these [0-9]+ paths will be fetched' "$log" || true)"
  if [ -n "$built" ]; then
    PROBE_REALIZED=true
    while IFS= read -r path; do
      [ -z "$path" ] && continue
      name="${path##*/}"
      name="${name%.drv}"
      # The store hash is exactly 32 characters and never contains '-', so the first '-' always
      # separates it from the derivation's own name.
      name="${name#*-}"
      if [[ "$name" =~ $PROBE_SOURCE_NAME_RE ]]; then
        PROBE_SOURCE+="${PROBE_SOURCE:+$'\n'}${path}"
      elif [[ "$name" =~ $PROBE_MINOR_NAME_RE ]]; then
        PROBE_MINOR+="${PROBE_MINOR:+$'\n'}${path}"
        PROBE_PREBUILT+="${PROBE_PREBUILT:+$'\n'}${path}"
      elif [[ "$name" =~ $PROBE_PREBUILT_NAME_RE ]]; then
        PROBE_PREBUILT+="${PROBE_PREBUILT:+$'\n'}${path}"
      fi
    done <<< "$built"
  fi
  if [ -n "$fetch_line" ]; then
    PROBE_REALIZED=true
    PROBE_FETCH_LINE="$fetch_line"
  fi
  PROBE_OK=true
  [ -n "$PROBE_SOURCE" ] && PROBE_OK=false
  rm -f "$log"
  return 0
}

pin_has_asset() {
  local system="$1" pin="${2:-}"
  [ -n "$pin" ] || pin="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/nix/aeneas-pin.json"
  command -v jq > /dev/null 2>&1 || return 1
  [ -f "$pin" ] || return 1
  [ -n "$(jq -r --arg s "$system" '.assets[$s] // empty' "$pin" 2>/dev/null)" ]
}

pin_source_known_broken() {
  local system="$1" pin="${2:-}"
  [ -n "$pin" ] || pin="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/nix/aeneas-pin.json"
  command -v jq > /dev/null 2>&1 || return 1
  [ -f "$pin" ] || return 1
  [ -n "$(jq -r --arg s "$system" '.source_build_known_broken[$s] // empty' "$pin" 2>/dev/null)" ]
}
