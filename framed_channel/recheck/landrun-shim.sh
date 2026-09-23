#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# landrun-shim.sh -- the landrun Comparator runs under the independent recheck (COMPARATOR_LANDRUN).
#
# INTERNAL: Comparator execs it in place of landrun during scripts/recheck-comparator.sh; not run by hand.
#
# This shim execs the real landrun with Comparator's own arguments, unchanged and in order, plus
# the extra grants Comparator's own sandbox omits but this project's build needs; the live,
# per-grant rationale is recorded in certificate/recheck.txt as a sandbox deviation and documented
# in certificate/README.md, "recheck.txt".
#
# When RECHECK_SHIM_LOG is set, each call appends `extra <grants added here>` and
# `comparator <Comparator's own arguments>` to it.
# Requires: Linux, bash, landrun, git, ldd, readelf. Exit: landrun's (0 for -h/--help).

set -u
# Comparator's first argument is always a landrun flag, never -h; answer it without side effects.
case "${1:-}" in
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
esac
tmp="$PWD/.lake/tmp"
mkdir -p "$tmp"
extra=(--env "TMPDIR=$tmp")
git_bin="$(realpath "$(command -v git)")"
for lib in $(ldd "$git_bin" | grep -oE '/[^ ]+\.so[^ ]*' | LC_ALL=C sort -u); do
  extra+=(--rox "$lib")
done
# RECHECK_LAKE_DIR (scripts/recheck-comparator.sh sets it when the toolchain's lake is nixpkgs'
# elan's shell wrapper) holds a `lake` symlink to the real binary; first on PATH, it is what
# landrun resolves Comparator's `lake build` to. `lake env` reorders PATH, so it is done here.
if [ -n "${RECHECK_LAKE_DIR:-}" ]; then
  PATH="$RECHECK_LAKE_DIR:$PATH"
  export PATH
fi
# CI, when the caller has it: Aeneas's lakefile precompiles AeneasMeta only where CI is unset, a
# room elaborates every lakefile afresh, and Comparator's sandbox passes on PATH, HOME and
# LEAN_ABORT_ON_PANIC only. Without this a room on a hosted runner configures the read-only
# linked Aeneas package differently from the tree that built it, and Lake tries to rebuild it in
# place (see confined() in scripts/recheck-comparator.sh). Unset stays unset.
if [ -n "${CI+x}" ]; then
  extra+=(--env "CI=$CI")
fi
# Execute on the ELF interpreter the toolchain's lake requests, resolved: on NixOS it is nix-ld,
# which landrun's -ldd does not grant, so the exec of lake itself is denied without it.
lake_bin="$(command -v lake || true)"
if [ -n "$lake_bin" ] && command -v readelf > /dev/null 2>&1; then
  interp="$(readelf -l "$lake_bin" 2>/dev/null | sed -n 's/.*program interpreter: \(.*\)\]$/\1/p')"
  [ -n "$interp" ] && [ -e "$interp" ] && extra+=(--rox "$(realpath "$interp")")
fi
if [ -n "${RECHECK_EXTRA_RWX:-}" ]; then
  mkdir -p "$RECHECK_EXTRA_RWX"
  extra+=(--rwx "$RECHECK_EXTRA_RWX")
fi
if [ -n "${RECHECK_SHIM_LOG:-}" ]; then
  printf 'extra %s\n' "${extra[*]}" >> "$RECHECK_SHIM_LOG"
  printf 'comparator %s\n' "$*" >> "$RECHECK_SHIM_LOG"
fi
exec landrun "${extra[@]}" "$@"
