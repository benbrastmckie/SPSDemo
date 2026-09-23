#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# recheck-kernel.sh -- replay the example's modules in Lean4Lean and in leanchecker.
#
# Per package (core; bridge with --bridge), after `lake build` of the package and its Challenge
# library, every module under its library root and Challenge library is replayed one per process:
#   lean4lean          Lean4Lean (the recheck/ build): re-typechecks the declarations the modules
#                      add, imports taken from .olean; a Lean port of the C++ kernel, auditing no
#                      axiom policy
#   leanchecker        the pinned toolchain's own checker: a same-kernel replay of the build
#   leanchecker-fresh  core: FramedChannel.Registry and its whole import closure, from Init
#   lean4lean-fresh    core, with --fresh only: the same in Lean4Lean (about 5 minutes)
# What each establishes and does not: certificate/README.md.
#
# Usage: bash scripts/recheck-kernel.sh --out DIR [--bridge] [--fresh] [-h | --help]
#   --out DIR   working directory (created): logs and DIR/kernel.verdicts, one line per checker
#               and package: `<checker> <pkg> <OK|FAIL|NOT-RUN> modules=<m> declarations=<n|->
#               <seconds> <note>`
#   --bridge    also the bridge package (needs aeneas/'s dependencies fetched)
#   --fresh     also lean4lean-fresh
#
# Requires: bash >= 4.4, the pinned Lean toolchain, the built recheck/ tools (recheck-revs.sh).
# A missing tool is NOT-RUN. Portable: unlike
# scripts/recheck-comparator.sh (Linux-only: needs a Landlock sandbox), this script uses no
# landrun/systemd-run/comparator and runs on any platform with the pinned toolchain (e.g. macOS
# via elan; exercised by .github/workflows/ci-macos-recheck.yml).
# Exit: 0 no line FAIL, 1 a line FAIL, 2 usage error.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out=""
bridge=false
fresh=false
while [ "$#" -gt 0 ]; do
  case "$1" in
    --out) [ "$#" -ge 2 ] || { echo "recheck-kernel.sh: --out needs a directory" >&2; exit 2; }; out="$2"; shift 2 ;;
    --bridge) bridge=true; shift ;;
    --fresh) fresh=true; shift ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "recheck-kernel.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done
[ -n "$out" ] || { echo "recheck-kernel.sh: --out DIR is required" >&2; exit 2; }
mkdir -p "$out"
out="$(cd "$out" && pwd)"

# shellcheck source=lib/recheck-revs.sh
. "$EX/scripts/lib/recheck-revs.sh"
# shellcheck source=lib/packages.sh
. "$EX/scripts/lib/packages.sh"
recheck_tool_paths

VERDICTS="$out/kernel.verdicts"
: > "$VERDICTS"
failures=0
line() {
  # line CHECKER PACKAGE VERDICT MODULES DECLARATIONS SECONDS NOTE
  printf '%s %s %s modules=%s declarations=%s %s %s\n' "$1" "$2" "$3" "$4" "$5" "$6" "$7" >> "$VERDICTS"
  [ "$3" = FAIL ] && failures=$((failures + 1))
  return 0
}

# modules_of DIR ROOTS...: module names of every .lean file under the roots, relative to DIR.
modules_of() {
  local dir="$1"; shift
  ( cd "$EX/$dir" && find "$@" -type f -name '*.lean' | sed -e 's/\.lean$//' -e 's|/|.|g' | LC_ALL=C sort )
}

# timed LOG CMD...: run CMD, logging to LOG; sets RC and SECS.
timed() {
  local log="$1"; shift
  local t0 t1
  t0="$(date +%s)"
  "$@" > "$log" 2>&1
  RC=$?
  t1="$(date +%s)"
  SECS=$((t1 - t0))
}

# lake_env DIR CMD...: run CMD through `lake env` from the package directory DIR.
lake_env() {
  local dir="$1"; shift
  ( cd "$dir" && exec lake env "$@" )
}

replay_package() {
  local pkg="$1" dir="$2" challenge="$3"
  shift 3
  local roots=("$@") mods n pdir="$EX/$dir"
  mods="$(modules_of "$dir" "${roots[@]}")"
  n="$(printf '%s\n' "$mods" | grep -c .)"
  printf '%s\n' "$mods" > "$out/modules.$pkg"

  if ! ( cd "$pdir" && lake build && lake build "$challenge" ) > "$out/build.$pkg.log" 2>&1; then
    for c in lean4lean leanchecker; do
      line "$c" "$pkg" FAIL "$n" - 0 "lake build of the $pkg package failed (see build.$pkg.log)"
    done
    return
  fi

  # Lean4Lean, one module per process: loading a Mathlib-sized environment for many modules in one
  # process needs tens of GB.
  if [ -z "$RECHECK_LEAN4LEAN" ]; then
    line lean4lean "$pkg" NOT-RUN "$n" - 0 "lean4lean not built (cd recheck && lake build lean4lean/lean4lean lean4export/lean4export)"
  else
    local total=0 secs=0 bad="" m d
    : > "$out/lean4lean.$pkg.log"
    for m in $mods; do
      timed "$out/lean4lean.$pkg.$m.log" lake_env "$pdir" "$RECHECK_LEAN4LEAN" "$m"
      secs=$((secs + SECS))
      d="$(sed -n 's/^checked \([0-9][0-9]*\) declarations$/\1/p' "$out/lean4lean.$pkg.$m.log" | tail -1)"
      echo "$m exit=$RC checked=${d:-none}" >> "$out/lean4lean.$pkg.log"
      if [ "$RC" -ne 0 ] || [ -z "$d" ]; then
        bad="$m (exit $RC; $(grep -v 'lean4lean took' "$out/lean4lean.$pkg.$m.log" | tail -1))"
        break
      fi
      total=$((total + d))
    done
    if [ -z "$bad" ]; then
      line lean4lean "$pkg" OK "$n" "$total" "$secs" "every declaration the listed modules add was re-typechecked; imports taken from .olean"
    else
      line lean4lean "$pkg" FAIL "$n" - "$secs" "$bad"
    fi
  fi

  # leanchecker, one module per process likewise
  if [ -z "$RECHECK_LEANCHECKER" ]; then
    line leanchecker "$pkg" NOT-RUN "$n" - 0 "leanchecker not found in the pinned toolchain"
  else
    local secs=0 bad="" m
    for m in $mods; do
      timed "$out/leanchecker.$pkg.$m.log" lake_env "$pdir" "$RECHECK_LEANCHECKER" "$m"
      secs=$((secs + SECS))
      if [ "$RC" -ne 0 ] || grep -q . "$out/leanchecker.$pkg.$m.log"; then
        bad="$m (exit $RC; $(tail -1 "$out/leanchecker.$pkg.$m.log"))"
        break
      fi
    done
    if [ -z "$bad" ]; then
      line leanchecker "$pkg" OK "$n" - "$secs" "same-kernel replay of the listed modules from .olean"
    else
      line leanchecker "$pkg" FAIL "$n" - "$secs" "$bad"
    fi
  fi
}

# ---------------------------------------------------------------------- core
replay_package core lean FramedChannelChallenge FramedChannel FramedChannelChallenge FramedChannelChallenge.lean

if [ -n "$RECHECK_LEANCHECKER" ] && ! grep -q '^leanchecker core FAIL' "$VERDICTS"; then
  timed "$out/leanchecker-fresh.core.log" lake_env "$EX/lean" "$RECHECK_LEANCHECKER" --fresh FramedChannel.Registry
  if [ "$RC" -eq 0 ] && ! grep -q . "$out/leanchecker-fresh.core.log"; then
    line leanchecker-fresh core OK 1 - "$SECS" "same-kernel replay of FramedChannel.Registry and its whole import closure, from Init"
  else
    line leanchecker-fresh core FAIL 1 - "$SECS" "exit $RC; $(tail -1 "$out/leanchecker-fresh.core.log")"
  fi
else
  line leanchecker-fresh core NOT-RUN 1 - 0 "leanchecker unavailable or the core replay failed"
fi

if $fresh; then
  if [ -z "$RECHECK_LEAN4LEAN" ]; then
    line lean4lean-fresh core NOT-RUN 1 - 0 "lean4lean not built"
  else
    timed "$out/lean4lean-fresh.core.log" lake_env "$EX/lean" "$RECHECK_LEAN4LEAN" --fresh FramedChannel.Registry
    decls="$(sed -n 's/^checked \([0-9][0-9]*\) declarations$/\1/p' "$out/lean4lean-fresh.core.log" | tail -1)"
    if [ "$RC" -eq 0 ] && [ -n "$decls" ]; then
      line lean4lean-fresh core OK 1 "$decls" "$SECS" "FramedChannel.Registry and its whole import closure (Init, Std, Lean) re-typechecked"
    else
      line lean4lean-fresh core FAIL 1 "${decls:--}" "$SECS" "exit $RC; $(grep -v 'lean4lean took' "$out/lean4lean-fresh.core.log" | tail -1)"
    fi
  fi
else
  line lean4lean-fresh core NOT-RUN 1 - 0 "not requested (check.sh --recheck-fresh; about 5 minutes)"
fi

# -------------------------------------------------------------------- bridge
bridge_skip=""
$bridge || bridge_skip="bridge package stage skipped"
[ -n "$bridge_skip" ] || bridge_deps_fetched || bridge_skip="bridge dependencies not fetched"
if [ -n "$bridge_skip" ]; then
  n="$(modules_of aeneas FramedChannelAeneas FramedChannelAeneasChallenge FramedChannelAeneasChallenge.lean | grep -c .)"
  line lean4lean bridge NOT-RUN "$n" - 0 "$bridge_skip"
  line leanchecker bridge NOT-RUN "$n" - 0 "$bridge_skip"
else
  replay_package bridge aeneas FramedChannelAeneasChallenge FramedChannelAeneas FramedChannelAeneasChallenge FramedChannelAeneasChallenge.lean
fi

cat "$VERDICTS"
[ "$failures" -eq 0 ]
