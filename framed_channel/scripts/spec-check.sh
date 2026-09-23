#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# spec-check.sh -- run the Specify checker over the statement-only Challenge libraries. READ-ONLY.
#
# Builds each package's Challenge library, elaborates `#spec_check`
# (lean/FramedChannel/SpecCheck.lean) over it and prints the records, prefixed with the package;
# check.sh and check-approvals.sh judge them. It writes nothing under certificate/.
#
#   <pkg> IMPURE <name> <kind>      a Challenge constant that is not a statement-only theorem
#   <pkg> stmt <name> <hash> <mod>  a restated theorem's statement hash and its Challenge module
#   <pkg> digest <module> <nat>     a Challenge module's closure digest (what an approval covers)
#   <pkg> reached <name>            an extracted definition some statement's closure reaches
#   <pkg> defs-thm <name>           a user-declared theorem inside a definitions module
#   <pkg> closure-thm <name>        a non-Challenge theorem of this example a statement depends on
#
# Usage: bash scripts/spec-check.sh (--core-only | --aeneas) [--log-dir DIR] [-h | --help]
#   --core-only    the core package only
#   --aeneas       also the bridge package, fetching its dependencies (about 7 GB) if absent
#   --log-dir DIR  keep each Challenge build log as DIR/challenge.<pkg>.log
#
# One of --core-only/--aeneas is required: this script no longer infers a scope from whether
# aeneas/'s dependencies happen to be fetched.
#
# Requires: bash >= 4.4, the Lean toolchain pinned in lean/lean-toolchain. A skipped bridge
# package prints `bridge skipped` on stderr.
# Exit: 0 every requested package checked (whatever the records say), 1 a build or elaboration
# failed, 2 usage error.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/packages.sh
. "$EX/scripts/lib/packages.sh"

log_dir=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --core-only|--aeneas) bridge_scope_arg spec-check.sh "$1" || exit $?; shift ;;
    --log-dir)
      [ "$#" -ge 2 ] || { echo "spec-check.sh: --log-dir needs a directory" >&2; exit 2; }
      log_dir="$2"; shift 2 ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "spec-check.sh: unknown argument '$1' (expected --core-only, --aeneas, --log-dir DIR)" >&2
       exit 2 ;;
  esac
done
if [ -z "${bridge_scope:-}" ]; then
  echo "spec-check.sh: give --core-only or --aeneas; neither infers a default any more" >&2
  exit 2
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
[ -n "$log_dir" ] || log_dir="$work"
mkdir -p "$log_dir"

# The checker itself lives in the core package; the bridge driver imports it through the
# `framed_channel` dependency, so it is built first.
if ! ( cd "$EX/lean" && lake build FramedChannel.SpecCheck ) > "$work/speccheck.build.log" 2>&1; then
  echo "spec-check.sh: could not build FramedChannel.SpecCheck" >&2
  tail -30 "$work/speccheck.build.log" >&2
  exit 1
fi

for name in "${PACKAGE_NAMES[@]}"; do
  dir="${PKG_DIR[$name]}"
  lib="${PKG_CHALLENGE[$name]}"
  if [ "$name" = bridge ] && ! bridge_enabled; then
    echo "spec-check.sh: bridge skipped (--core-only)" >&2
    continue
  fi
  pkg="$EX/$dir"
  build_log="$log_dir/challenge.$name.log"
  if ! ( cd "$pkg" && lake build "$lib" ) > "$build_log" 2>&1; then
    echo "spec-check.sh: could not build the $name Challenge library $lib" >&2
    grep -vE '^(✔|⣿|trace)' "$build_log" | tail -40 >&2
    exit 1
  fi
  driver="$work/SpecCheckDriver_$name.lean"
  {
    echo "import $lib"
    echo "import FramedChannel.SpecCheck"
    echo
    echo "open FramedChannel.SpecCheck in"
    echo "#spec_check $lib"
  } > "$driver"
  if ! ( cd "$pkg" && lake env lean "$driver" ) > "$work/out.$name" 2>&1; then
    echo "spec-check.sh: the $name Specify checker did not elaborate" >&2
    tail -30 "$work/out.$name" >&2
    exit 1
  fi
  # Only records; anything else the elaborator printed is a tool failure.
  if grep -vqE '^(IMPURE|stmt|digest|reached|defs-thm|closure-thm) ' "$work/out.$name"; then
    echo "spec-check.sh: unexpected output from the $name Specify checker:" >&2
    grep -vE '^(IMPURE|stmt|digest|reached|defs-thm|closure-thm) ' "$work/out.$name" | head -20 >&2
    exit 1
  fi
  sed "s/^/$name /" "$work/out.$name"
done
exit 0
