#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/pre-push-hook/run.sh -- fixture tests for ../../.githooks/pre-push's exit-code mapping
# and argument vector, without ever running a real check.sh --core-only.
#
# Provides a stub `nix` on PATH (records the `nix develop ... --command ...` argument vector to a
# log file and exits with a per-case configured code, standing in for what a real
# `nix develop ... --command bash check.sh --core-only` would itself exit) and drives the hook
# through PATH manipulation, SKIP_CORE_ONLY_HOOK, and PRE_PUSH_HOOK_TEST_NIX_DAEMON_PROFILE (the
# hook's own test-only override of the fixed Nix-daemon-profile path it otherwise falls back to,
# so the "nix absent" case below stays hermetic even on a host that really does have a multi-user
# Nix daemon profile at that fixed path).
#
# Cases:
#   1. stub exits 3                 -> hook exits 0 (the pre-check's own by-design INCOMPLETE)
#   2. stub exits 0                 -> hook exits non-zero, naming the "PASS without the bridge"
#                                       condition specifically
#   3. stub exits 1                 -> hook exits non-zero, naming exit code 1
#   4. stub exits 2                 -> hook exits non-zero, naming exit code 2
#   5. SKIP_CORE_ONLY_HOOK=1        -> hook exits 0, and the stub is never invoked at all
#   6. nix absent from PATH (and the daemon-profile override points at a nonexistent file)
#                                    -> hook exits non-zero with the actionable message
#   7. the argument vector reaching the stub carries both --core-only and the #build attribute
#   8. a PATH directory providing an `aeneas` executable is dropped for the run, and the hook
#        still proceeds -- the developer-machine leak the filter exists to close (a user-profile
#        aeneas whose revision does not match the pin would otherwise fail check.sh's coherence
#        stage, which the CI leg never reaches because a runner has no such profile)
#
# Usage: bash tests/pre-push-hook/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
HOOK="$EX/../.githooks/pre-push"

if [ ! -f "$HOOK" ]; then
  echo "tests/pre-push-hook: .githooks/pre-push not found relative to the repository root" >&2
  exit 2
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

bin="$work/bin"
mkdir -p "$bin"
cat > "$bin/nix" <<'STUB'
#!/usr/bin/env bash
# Stub nix for tests/pre-push-hook/run.sh. Records the develop invocation's argument vector and
# exits with NIX_STUB_DEVELOP_EXIT rather than actually running the wrapped command -- standing
# in for whatever check.sh --core-only itself would have exited.
set -u
case "${1:-}" in
  develop)
    shift
    printf '%s\n' "$*" >> "$NIX_STUB_LOG"
    exit "${NIX_STUB_DEVELOP_EXIT:-0}"
    ;;
  *)
    echo "stub nix: unhandled subcommand '${1:-}'" >&2
    exit 1
    ;;
esac
STUB
chmod +x "$bin/nix"

# A guaranteed-nonexistent path, so the "nix absent" case's daemon-profile fallback is a reliable
# no-op regardless of what the real fixed path holds on the machine running this suite.
missing_daemon_profile="$work/no-such-nix-daemon-profile.sh"

# The stub `nix` takes priority; the rest of the real PATH stays reachable for dirname/awk/etc.
path_with_stub="$bin:$PATH"

# The real PATH with every directory that holds an executable named `nix` removed, so the
# "nix absent" case is a faithful absence rather than merely a PATH ordering trick, while
# dirname/awk/etc. remain reachable. Deliberately not `env -i`'s fully empty PATH: that would
# also hide the ordinary utilities the hook itself needs before it ever gets to the nix check.
path_no_nix=""
IFS=':' read -ra _path_dirs <<< "$PATH"
for _d in "${_path_dirs[@]}"; do
  [ -n "$_d" ] || continue
  [ -x "$_d/nix" ] && continue
  path_no_nix="$path_no_nix:$_d"
done
path_no_nix="${path_no_nix#:}"

# A directory that provides an `aeneas` executable, standing in for the user profile a developer
# machine may carry. Never executed: the hook only ever tests -x on it, so an empty executable is
# a faithful stand-in for a real (mismatched-revision) aeneas.
leak="$work/leaked-profile-bin"
mkdir -p "$leak"
: > "$leak/aeneas"
chmod +x "$leak/aeneas"
path_with_leak="$bin:$leak:$PATH"

real_bash="$(command -v bash)"
failures=0
case_num=0

# run_case NAME "ENV1=v1 ENV2=v2 ..." PATH_VALUE WANT_EXIT WANT_TEXT WANT_DEVELOP
#   PATH_VALUE     the PATH the hook runs under ($path_with_stub, or $path_no_nix for "nix absent")
#   WANT_TEXT      a substring that must appear in combined stdout+stderr ("" to skip)
#   WANT_DEVELOP   a substring the develop log must contain, "NONE" to assert it stayed empty
#                  (nix's develop subcommand never invoked), or "" to skip the check
run_case() {
  local name="$1" envs="$2" path_value="$3" want_exit="$4" want_text="$5" want_develop="$6"
  case_num=$((case_num + 1))
  local logf="$work/develop-$case_num.log"
  : > "$logf"

  local out rc
  # shellcheck disable=SC2086
  out="$(env PATH="$path_value" NIX_STUB_LOG="$logf" \
    PRE_PUSH_HOOK_TEST_NIX_DAEMON_PROFILE="$missing_daemon_profile" $envs \
    "$real_bash" "$HOOK" origin "git@example.invalid:x.git" 2>&1)"
  rc=$?

  local ok=1
  if [ "$rc" -ne "$want_exit" ]; then ok=0; fi
  if [ -n "$want_text" ] && ! grep -qF -- "$want_text" <<< "$out"; then ok=0; fi
  if [ "$want_develop" = "NONE" ]; then
    if [ -s "$logf" ]; then ok=0; fi
  elif [ -n "$want_develop" ]; then
    grep -qF -- "$want_develop" "$logf" || ok=0
  fi

  if [ "$ok" -eq 1 ]; then
    echo "[ok] $name (exit $rc)"
  else
    echo "[FAIL] $name: exit $rc (want $want_exit)"
    echo "  develop log:"; sed 's/^/    /' "$logf"
    echo "  output:"; sed 's/^/    /' <<< "$out"
    failures=$((failures + 1))
  fi
}

# 1. The pre-check's own by-design INCOMPLETE: exit 3 is the pass condition.
run_case "stub exits 3 -> hook exits 0 (push proceeds)" \
  "NIX_STUB_DEVELOP_EXIT=3" "$path_with_stub" 0 "INCOMPLETE (exit 3) by design; push proceeding" "--core-only"

# 2. An unexpected PASS (exit 0) is a defect signal, not a green light -- must abort and must
# name the "PASS without the bridge" condition specifically, not just a generic non-3 message.
run_case "stub exits 0 -> hook aborts, naming PASS without the bridge" \
  "NIX_STUB_DEVELOP_EXIT=0" "$path_with_stub" 1 "an exit 0 here would mean check.sh claimed PASS without the bridge" ""

# 3. A real FAIL (exit 1) aborts and names the exit code.
run_case "stub exits 1 -> hook aborts, naming exit 1" \
  "NIX_STUB_DEVELOP_EXIT=1" "$path_with_stub" 1 "check.sh --core-only exited 1" ""

# 4. A usage error (exit 2) aborts and names the exit code.
run_case "stub exits 2 -> hook aborts, naming exit 2" \
  "NIX_STUB_DEVELOP_EXIT=2" "$path_with_stub" 1 "check.sh --core-only exited 2" ""

# 5. The documented skip hatch: exits 0 and never touches nix at all (log stays empty).
run_case "SKIP_CORE_ONLY_HOOK=1 -> hook exits 0, stub never invoked" \
  "SKIP_CORE_ONLY_HOOK=1 NIX_STUB_DEVELOP_EXIT=3" "$path_with_stub" 0 "SKIP_CORE_ONLY_HOOK=1 is set" "NONE"

# 6. nix entirely absent from PATH, and the (overridden-for-this-test) daemon profile script does
# not exist either -> the hook must abort with its actionable message, never silently pass.
run_case "nix absent from PATH -> hook aborts with actionable message" \
  "" "$path_no_nix" 1 "nix is not on PATH and could not be resolved" "NONE"

# 7. The argument vector reaching the stub carries both --core-only and the #build attribute --
# reusing case 1's log (any exit-3 run proves this).
run_case "argument vector carries --core-only and #build" \
  "NIX_STUB_DEVELOP_EXIT=3" "$path_with_stub" 0 "" "#build"
grep -qF -- "--core-only" "$work/develop-$case_num.log" || {
  echo "[FAIL] argument vector carries --core-only: not found in $work/develop-$case_num.log"
  failures=$((failures + 1))
}

# 8. A PATH entry providing aeneas is dropped before nix is invoked, and the run still proceeds.
# Without the filter this leaked binary reaches check.sh's aeneas revision coherence stage, which
# FAILS a revision that is not a prefix of the pin (scripts/lib/aeneas-revs.sh) while SKIPPING an
# absent one -- so the push would abort for a condition --core-only does not even establish.
run_case "aeneas-providing PATH entry is dropped -> hook still proceeds" \
  "NIX_STUB_DEVELOP_EXIT=3" "$path_with_leak" 0 "dropping '$leak' from PATH for this run" "--core-only"

if [ "$failures" -ne 0 ]; then
  echo "tests/pre-push-hook: $failures of $case_num case(s) failed"
  exit 1
fi
echo "tests/pre-push-hook: all $case_num cases pass"
