#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# refresh-hashes.sh -- regenerate the statement-hash column of every registry.
#
# Each `register%` row pins the structural hash of its theorem's statement
# (lean/FramedChannel/Certify.lean). Run after deliberately changing a registered statement or
# bumping the toolchain, and re-read the diff: every changed number is a changed statement. The
# core registry goes first, because the bridge registry imports it.
#
# Usage: bash scripts/refresh-hashes.sh [--check] (--aeneas | --core-only) [-h | --help] (from framed_channel/)
#   --check       rewrite nothing; print what would change (check.sh's statement-hash stage)
#   --aeneas      include the bridge registry, fetching its dependencies (about 7 GB) if absent
#   --core-only   never touch the bridge registry
#
# One of --aeneas/--core-only is required: this script no longer infers a scope from whether
# aeneas/'s dependencies happen to be fetched.
#
# Requires: bash >= 4.4, perl, the Lean toolchain pinned in lean/lean-toolchain.
# Exit: 0 current (or rewritten), 1 stale under --check or a build failed, 2 usage error.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/packages.sh
. "$EX/scripts/lib/packages.sh"

# An unrecognised argument must not fall through to the in-place rewrite: a mistyped `--check`
# would then silently rewrite a registry when a read-only check was intended.
check_only=false
for arg in "$@"; do
  case "$arg" in
    --check) check_only=true ;;
    --aeneas|--core-only) bridge_scope_arg refresh-hashes.sh "$arg" || exit $? ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "refresh-hashes.sh: unknown argument '$arg' (expected --check, --aeneas, --core-only)" >&2
       exit 2 ;;
  esac
done
if [ -z "${bridge_scope:-}" ]; then
  echo "refresh-hashes.sh: give --aeneas or --core-only; neither infers a default any more" >&2
  exit 2
fi

# Every temporary path, removed once however the run ends.
tmp_paths=()
cleanup() {
  local p
  for p in "${tmp_paths[@]}"; do rm -rf "$p"; done
}
trap cleanup EXIT

# refresh_registry NAME: regenerate (or, under --check, compare) one registry's hash column.
# Returns 0 when current (or rewritten), 1 when stale under --check, 2 on a tool failure.
refresh_registry() {
  local name="$1" rel="${PKG_REGISTRY[$1]}" ns="${PKG_NS[$1]}"
  local reg="$EX/$rel" pkg="$EX/${PKG_DIR[$1]}"
  local gendir="$pkg/.hashgen" gen names imports out rc tmp hashes changed

  names="$(registry_rows "$name" | cut -d' ' -f1)"
  if [ -z "$names" ]; then
    echo "refresh-hashes.sh: no register% rows found in $rel" >&2
    return 2
  fi

  gen="$gendir/Gen.lean"
  tmp="$(mktemp)"
  hashes="$(mktemp)"
  tmp_paths+=("$gendir" "$tmp" "$hashes")
  mkdir -p "$gendir"
  {
    # Import exactly what the registry imports, minus the registry itself.
    lean_imports "$reg" | sed 's/^/import /'
    echo
    echo "namespace $ns"
    echo "open FramedChannel.Certify"
    echo
    for n in $names; do
      echo "#eval IO.println s!\"$n {stmt_hash% $n}\""
    done
    echo
    echo "end $ns"
  } > "$gen"

  # The generator only imports what the registry imports, so build exactly those modules first.
  # The registry itself is deliberately not built here: while its hashes are stale it does not
  # elaborate, and that is the situation this script exists to repair.
  imports="$(lean_imports "$reg")"
  # shellcheck disable=SC2086
  if ! ( cd "$pkg" && lake build $imports > /dev/null 2>&1 ); then
    echo "refresh-hashes.sh: could not build the $name registry's imports" >&2
    # shellcheck disable=SC2086
    ( cd "$pkg" && lake build $imports 2>&1 | tail -20 ) >&2
    return 2
  fi

  out="$(cd "$pkg" && lake env lean --root=. "$gen" 2>&1)"
  rc=$?
  rm -rf "$gendir"
  if [ $rc -ne 0 ]; then
    echo "refresh-hashes.sh: could not elaborate the $name statement-hash generator" >&2
    echo "$out" >&2
    return 2
  fi

  echo "$out" | grep -E '^[A-Za-z_][A-Za-z0-9_.]* [0-9]+$' > "$hashes"
  if [ ! -s "$hashes" ]; then
    echo "refresh-hashes.sh: the $name generator printed no name/hash pairs" >&2
    return 2
  fi

  # One pass over the file carrying the whole name -> hash map. The hash is the token immediately
  # after the `verified` boolean, always on the row's first line, so the substitution is anchored
  # and unambiguous; a row whose name the generator did not report is left exactly as it was.
  cp "$reg" "$tmp"
  HASHES="$hashes" perl -i -pe '
    BEGIN {
      open my $fh, "<", $ENV{HASHES} or die "refresh-hashes.sh: $!";
      while (<$fh>) { my ($n, $h) = split; $map{$n} = $h; }
    }
    s{(register%\s+([A-Za-z_][A-Za-z0-9_.]*)\s+\S+\s+\S+\s+(?:true|false)\s+)\d+}
     {exists $map{$2} ? "$1$map{$2}" : $&}e;
  ' "$tmp"

  changed=0
  cmp -s "$tmp" "$reg" || changed=1

  if $check_only; then
    if [ $changed -eq 1 ]; then
      diff -u "$reg" "$tmp" | sed -n '1,200p'
      echo "refresh-hashes.sh: $name statement hashes are stale; run 'bash scripts/refresh-hashes.sh'" >&2
      return 1
    fi
    echo "refresh-hashes.sh: $name statement hashes are current ($rel)"
    return 0
  fi

  cp "$tmp" "$reg"
  if [ $changed -eq 1 ]; then
    echo "refresh-hashes.sh: rewrote the statement-hash column of $rel"
  else
    echo "refresh-hashes.sh: $name statement hashes already current (no change)"
  fi
  return 0
}

status=0
for name in "${PACKAGE_NAMES[@]}"; do
  if [ "$name" = bridge ] && ! bridge_enabled; then
    echo "refresh-hashes.sh: bridge registry skipped (--core-only)"
    continue
  fi
  refresh_registry "$name"
  rc=$?
  if [ $rc -eq 2 ]; then
    exit 1
  fi
  if [ $rc -ne 0 ]; then
    status=1
    # A stale core registry does not elaborate, so the bridge generator (which imports it) cannot
    # run meaningfully until the core column is refreshed.
    [ "$name" = core ] && break
  fi
done
exit $status
