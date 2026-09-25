#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/launcher-compat/run.sh -- the three outside-Nix launchers (full-gate.sh, install.sh,
# .githooks/pre-push) and everything they source must run under the host bash, which on macOS is
# /bin/bash 3.2.57. Every other script in this repository runs inside a Nix dev shell and sees
# Nix's bash 5; these do not -- .githooks/pre-push in particular runs at push time, before any
# `nix develop` shell has been entered at all.
#
# Two passes:
#   static   over the launcher set (full-gate.sh, install.sh, .githooks/pre-push, each file they
#            `.`-source, and the composite actions' scripts -- lean-toolchain/verify.sh,
#            mathlib-cache/get.sh, precheck-incomplete/run.sh -- which a macOS runner also runs
#            under /bin/bash):
#            no bash-4-only construct (mapfile, associative arrays, namerefs, case-modification
#            expansions, `|&`, `&>>`, coproc, `wait -n`, `${x@Q}`, `[[ -v`, negative subscripts,
#            `;&`/`;;&`), no array expansion outside the 3.2-safe `${arr[@]+"${arr[@]}"}` form
#            (a bare "${arr[@]}" on an empty array is an unbound-variable error under `set -u`
#            before bash 4.4), no sourced file missing from the set, and no drift between
#            full-gate.sh's own bridge_deps_fetched and packages.sh's. Reports file:line.
#   dynamic  under ${LAUNCHER_COMPAT_BASH:-/bin/bash}, when that interpreter exists: runs
#            `full-gate.sh --support-level`, `full-gate.sh --help`, `install.sh --help`, and
#            full-gate.sh end to end against a stub `nix` (with and without pass-through
#            arguments, the empty-array path), asserting exit 0, the route=/gate= lines, the
#            argument vector reaching check.sh, and an EMPTY stderr -- a bash-4 builtin option
#            is a non-fatal error under 3.2, so a clean exit code alone proves nothing.
#
# An in-Nix fixture can never observe the host bash, so the faithful run is the `launcher-compat`
# job in .github/workflows/ci-macos.yml, which invokes this file with /bin/bash on real macOS
# runners. This file is itself part of the scanned set and must stay 3.2-compatible.
#
# Environment:
#   LAUNCHER_COMPAT_BASH              interpreter for the dynamic pass (default /bin/bash)
#   LAUNCHER_COMPAT_REQUIRE_DYNAMIC   when 1, a missing interpreter is a failure, not a [skip]
#   LAUNCHER_COMPAT_EXPECT_BASH       when set, the interpreter's BASH_VERSION must start with it
#   LAUNCHER_COMPAT_EXPECT_GATE       when set, --support-level must print gate=<this>
#
# Usage: bash tests/launcher-compat/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 3.2, awk, grep, sed. No Nix, no jq.
# Exit: 0 every check passes, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"

# The launcher set, relative to the repository root, one per line. No arrays in this file.
# The two composite-action scripts (lean-toolchain/verify.sh, mathlib-cache/get.sh) are here
# because a composite action's `shell: bash` on a macOS runner is the same /bin/bash 3.2, outside
# any Nix shell.
LAUNCHERS="full-gate.sh
install.sh
.githooks/pre-push
nix/heavy-build-probe.sh
nix/lean-toolchain-pin.sh
nix/nix-version-floor.sh
.github/actions/lean-toolchain/verify.sh
.github/actions/mathlib-cache/get.sh
.github/actions/precheck-incomplete/run.sh
framed_channel/tests/launcher-compat/run.sh"

failures=0
fail() { echo "[FAIL] $*"; failures=$((failures + 1)); }
ok() { echo "[ok] $*"; }

# ------------------------------------------------------------------------------ static
# Lines carrying the marker below are exempt: they are this file's own pattern definitions.
BASH4_RE='mapfile|readarray|(declare|local|typeset)[[:space:]]+-[A-Za-z]*[Ang]|\$\{[A-Za-z_][A-Za-z0-9_]*(,,|\^\^|,|\^)\}|\|&|&>>|coproc|wait[[:space:]]+-n|\$\{[A-Za-z_][A-Za-z0-9_]*@[A-Za-z]\}|\[\[[[:space:]]+-v[[:space:]]|\[-[0-9]+\]|;;&|;&' # launcher-compat-ignore
GUARDED_RE='\$\{[A-Za-z_][A-Za-z0-9_]*\[[@*]\]\+"\$\{[A-Za-z_][A-Za-z0-9_]*\[[@*]\]\}"\}' # launcher-compat-ignore
ANY_ARRAY_RE='\$\{[A-Za-z_][A-Za-z0-9_]*\[[@*]\]' # launcher-compat-ignore

# code_lines FILE: "N:text" for every line that is neither a comment nor marker-exempt.
code_lines() {
  awk '/launcher-compat-ignore/ { next } /^[[:space:]]*#/ { next } { print NR ":" $0 }' "$1"
}

static_failures_before=$failures
for rel in $LAUNCHERS; do
  f="$ROOT/$rel"
  if [ ! -f "$f" ]; then
    fail "launcher set names a file that does not exist: $rel"
    continue
  fi
  hits="$(code_lines "$f" | grep -E -- "$BASH4_RE" || true)"
  if [ -n "$hits" ]; then
    while IFS= read -r h; do fail "bash-4-only construct at $rel:$h"; done <<EOF
$hits
EOF
  fi
  hits="$(code_lines "$f" | sed -E "s/$GUARDED_RE//g" | grep -E -- "$ANY_ARRAY_RE" || true)"
  if [ -n "$hits" ]; then
    while IFS= read -r h; do
      fail "array expansion outside the 3.2-safe guarded form at $rel:$h"
    done <<EOF
$hits
EOF
  fi
  # Every file a launcher sources must itself be in the launcher set.
  sourced="$(code_lines "$f" | sed -n -E 's/^[0-9]+:[[:space:]]*(\.|source)[[:space:]]+"?\$\{?ROOT\}?\/([^"[:space:]]+)"?.*$/\2/p')"
  for s in $sourced; do
    case "
$LAUNCHERS
" in
      *"
$s
"*) ;;
      *) fail "$rel sources $s, which is not in the launcher set (add it, or stop sourcing it)" ;;
    esac
  done
done

# full-gate.sh carries its own bridge_deps_fetched because it cannot source packages.sh (which
# needs associative arrays). The two must test the same directories.
twin_dirs() {
  awk '/^bridge_deps_fetched\(\)/ { p = 1 } p { print } p && /^}/ { exit }' "$1" |
    grep -oE 'aeneas/\.lake/packages/[A-Za-z0-9_-]+' | LC_ALL=C sort -u
}
gate_dirs="$(twin_dirs "$ROOT/full-gate.sh")"
pkg_dirs="$(twin_dirs "$ROOT/framed_channel/scripts/lib/packages.sh")"
if [ -z "$gate_dirs" ] || [ "$gate_dirs" != "$pkg_dirs" ]; then
  fail "bridge_deps_fetched drifted: full-gate.sh tests [$(printf '%s' "$gate_dirs" | tr '\n' ' ')], packages.sh tests [$(printf '%s' "$pkg_dirs" | tr '\n' ' ')]"
fi

if [ "$failures" -eq "$static_failures_before" ]; then
  ok "static: no bash-4-only construct or unguarded array expansion in the launcher set"
fi

# ------------------------------------------------------------------------------ dynamic
B="${LAUNCHER_COMPAT_BASH:-/bin/bash}"
if [ ! -x "$B" ]; then
  if [ "${LAUNCHER_COMPAT_REQUIRE_DYNAMIC:-0}" = 1 ]; then
    fail "dynamic: interpreter '$B' does not exist (LAUNCHER_COMPAT_REQUIRE_DYNAMIC=1)"
  else
    echo "[skip] dynamic: interpreter '$B' does not exist (set LAUNCHER_COMPAT_BASH)"
  fi
else
  bver="$("$B" -c 'echo "$BASH_VERSION"' 2>/dev/null)"
  echo "dynamic: interpreter $B reports BASH_VERSION=$bver"
  if [ -n "${LAUNCHER_COMPAT_EXPECT_BASH:-}" ]; then
    case "$bver" in
      "$LAUNCHER_COMPAT_EXPECT_BASH"*) ok "dynamic: interpreter version starts with $LAUNCHER_COMPAT_EXPECT_BASH" ;;
      *) fail "dynamic: interpreter version '$bver' does not start with '$LAUNCHER_COMPAT_EXPECT_BASH'" ;;
    esac
  fi

  work="$(mktemp -d)"
  trap 'rm -rf "$work"' EXIT

  # dyn NAME WANT_STDOUT_SUBSTRING -- COMMAND...: exit 0, substring present, stderr empty.
  dyn() {
    local name="$1" want="$2" rc
    shift 3
    "$@" > "$work/out" 2> "$work/err"
    rc=$?
    if [ "$rc" -ne 0 ]; then
      fail "dynamic: $name: exit $rc (want 0)"; sed 's/^/    /' "$work/err"
    elif [ -s "$work/err" ]; then
      fail "dynamic: $name: stderr is not empty:"; sed 's/^/    /' "$work/err"
    elif [ -n "$want" ] && ! grep -qF -- "$want" "$work/out"; then
      fail "dynamic: $name: stdout lacks '$want':"; sed 's/^/    /' "$work/out"
    else
      ok "dynamic: $name"
    fi
  }

  dyn "full-gate.sh --support-level prints route=" "route=" -- "$B" "$ROOT/full-gate.sh" --support-level
  dyn "full-gate.sh --support-level prints gate=" "gate=" -- "$B" "$ROOT/full-gate.sh" --support-level
  if [ -n "${LAUNCHER_COMPAT_EXPECT_GATE:-}" ]; then
    dyn "full-gate.sh --support-level prints gate=$LAUNCHER_COMPAT_EXPECT_GATE" \
      "gate=$LAUNCHER_COMPAT_EXPECT_GATE" -- "$B" "$ROOT/full-gate.sh" --support-level
  fi
  dyn "full-gate.sh --help" "Usage: bash full-gate.sh" -- "$B" "$ROOT/full-gate.sh" --help
  dyn "install.sh --help" "install.sh" -- "$B" "$ROOT/install.sh" --help

  # End to end against a stub nix: reaches both `exec nix develop` lines' array expansions.
  mkdir -p "$work/bin"
  cat > "$work/bin/nix" <<'STUB'
#!/bin/sh
case "${1:-}" in
  --version) echo "nix (Nix) 2.24.9"; exit 0 ;;
  build) exit 0 ;;
  develop) shift; echo "$*" >> "$NIX_STUB_LOG"; exit 0 ;;
  *) echo "stub nix: unhandled subcommand '${1:-}'" >&2; exit 1 ;;
esac
STUB
  chmod +x "$work/bin/nix"
  printf '{"assets":{},"source_build_known_broken":{}}\n' > "$work/pin.json"

  # gate_case NAME WANT_IN_DEVELOP_LOG SYSTEM ARGS...
  gate_case() {
    local name="$1" want="$2" system="$3"
    shift 3
    : > "$work/develop.log"
    dyn "$name" "" -- env PATH="$work/bin:$PATH" NIX_STUB_LOG="$work/develop.log" \
      FULL_GATE_TEST_SYSTEM="$system" FULL_GATE_TEST_PIN="$work/pin.json" \
      FULL_GATE_TEST_BRIDGE_FETCHED=1 "$B" "$ROOT/full-gate.sh" "$@"
    if ! grep -qF -- "$want" "$work/develop.log"; then
      fail "dynamic: $name: nix develop was not invoked with '$want':"
      sed 's/^/    /' "$work/develop.log"
    fi
  }
  # x86_64-darwin always takes the committed-extraction line; the empty pin sends x86_64-linux
  # down the consented from-source line. Between them both `exec nix develop` sites run.
  gate_case "full gate, committed-extraction line, no pass-through arguments" \
    "check.sh --committed-extraction" x86_64-darwin --yes
  gate_case "full gate, committed-extraction line, pass-through arguments" \
    "check.sh --committed-extraction --clean" x86_64-darwin --yes -- --clean
  gate_case "full gate, gate line, no pass-through arguments" \
    "framed_channel/check.sh" x86_64-linux --yes
  gate_case "full gate, gate line, pass-through arguments" \
    "check.sh --clean --lean-only" x86_64-linux --yes -- --clean --lean-only
fi

if [ "$failures" -ne 0 ]; then
  echo "tests/launcher-compat: $failures check(s) failed"
  exit 1
fi
echo "tests/launcher-compat: all checks pass"
