#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/full-gate/run.sh -- fixture tests for full-gate.sh's fallback chain, consent rules and
# probe-driven cost reporting, without ever running a real Nix build.
#
# Provides a stub `nix` on PATH (records every `nix develop`/`nix build --dry-run` invocation to
# a log file, and prints canned `nix build --dry-run` output driven by NIX_STUB_DRYRUN_MODE) and a
# stub nix/aeneas-pin.json per case, then drives full-gate.sh through its FULL_GATE_TEST_* test
# hooks (FULL_GATE_TEST_SYSTEM, FULL_GATE_TEST_PIN, FULL_GATE_TEST_TTY,
# FULL_GATE_TEST_BRIDGE_FETCHED -- see full-gate.sh's own comments at each hook) to reach every
# branch of the fallback chain from one real (x86_64-linux) machine, plus --support-level's
# route/gate/recheck resolution across all four designated systems (never touches the stub `nix`
# at all: --support-level exits before the probe).
#
# Usage: bash tests/full-gate/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, jq.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

if ! command -v jq > /dev/null 2>&1; then
  echo "tests/full-gate: jq is not on PATH; run inside nix develop" >&2
  exit 2
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
GATE="$EX/../full-gate.sh"
PROBE="$EX/../nix/heavy-build-probe.sh"

if [ ! -f "$GATE" ] || [ ! -f "$PROBE" ]; then
  echo "tests/full-gate: full-gate.sh or nix/heavy-build-probe.sh not found relative to the repository root" >&2
  exit 2
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# A minimal repository tree: full-gate.sh and nix/heavy-build-probe.sh. full-gate.sh defines its
# own bridge_deps_fetched (it must not source packages.sh: see its comment there), and every case
# below overrides that check through FULL_GATE_TEST_BRIDGE_FETCHED anyway.
tree="$work/tree"
mkdir -p "$tree/nix"
cp "$GATE" "$tree/full-gate.sh"
cp "$PROBE" "$tree/nix/heavy-build-probe.sh"
chmod +x "$tree/full-gate.sh"

# Complete pin: all three systems, nothing known-broken.
cat > "$tree/nix/pin-complete.json" <<'EOF'
{
  "assets": {
    "x86_64-linux": {"name": "a", "sha256": "x"},
    "aarch64-linux": {"name": "a", "sha256": "x"},
    "aarch64-darwin": {"name": "a", "sha256": "x"}
  },
  "source_build_known_broken": {},
  "macos_fallback": false
}
EOF
# Linux-complete only: no darwin asset, not known broken. macos_fallback: true mirrors the real
# nix/aeneas-pin.json field a pin bump sets when it drops the darwin asset.
cat > "$tree/nix/pin-no-darwin.json" <<'EOF'
{
  "assets": {
    "x86_64-linux": {"name": "a", "sha256": "x"},
    "aarch64-linux": {"name": "a", "sha256": "x"}
  },
  "source_build_known_broken": {},
  "macos_fallback": true
}
EOF
# Linux-complete only, darwin from-source recorded known-broken.
cat > "$tree/nix/pin-darwin-broken.json" <<'EOF'
{
  "assets": {
    "x86_64-linux": {"name": "a", "sha256": "x"},
    "aarch64-linux": {"name": "a", "sha256": "x"}
  },
  "source_build_known_broken": {"aarch64-darwin": "upstream's darwin release job failed for this tag"}
}
EOF

bin="$work/bin"
mkdir -p "$bin"
cat > "$bin/nix" <<'STUB'
#!/usr/bin/env bash
# Stub nix for tests/full-gate/run.sh. Records every invocation; `build --dry-run` output is
# driven by NIX_STUB_DRYRUN_MODE ("prebuilt", "source", "minor", "empty", "fail").
set -u
case "${1:-}" in
  build)
    shift
    installable=""
    for a in "$@"; do
      case "$a" in *#*) installable="$a" ;; esac
    done
    echo "$installable" >> "$NIX_STUB_LOG/build-calls.log"
    case "${NIX_STUB_DRYRUN_MODE:-empty}" in
      fail) exit 1 ;;
      source)
        cat <<'EOF'
these 2 derivations will be built:
  /nix/store/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-charon.drv
  /nix/store/bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb-ocaml5.2.1-aeneas-0.1.0.drv
these 3 paths will be fetched (10.0 MiB download, 20.0 MiB unpacked):
  /nix/store/cccccccccccccccccccccccccccccccc-foo
EOF
        ;;
      prebuilt)
        cat <<'EOF'
these 2 derivations will be built:
  /nix/store/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-aeneas-prebuilt-0-test.drv
  /nix/store/bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb-aeneas-mir-sysroot.drv
these 175 paths will be fetched (281.8 MiB download, 925.0 MiB unpacked):
  /nix/store/cccccccccccccccccccccccccccccccc-foo
EOF
        ;;
      minor)
        cat <<'EOF'
these 1 derivations will be built:
  /nix/store/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-comparator-test.drv
these 5 paths will be fetched (1.0 MiB download, 2.0 MiB unpacked):
  /nix/store/cccccccccccccccccccccccccccccccc-foo
EOF
        ;;
      empty) : ;;
    esac
    exit 0
    ;;
  develop)
    shift
    echo "$*" >> "$NIX_STUB_LOG/develop-calls.log"
    # full-gate.sh's own Lean toolchain pin check (lean_pin_check) makes its own "nix develop
    # .#build --command bash .../nix/lean-toolchain-pin.sh" call before the real one below, on
    # every route -- always succeeds here, since what it verifies is covered end to end by
    # tests/lean-toolchain-pin/run.sh, not this fixture, and NIX_STUB_DEVELOP_EXIT below stands
    # in for the *real* check.sh invocation's exit code, which the pin check is not.
    case "$*" in
      *lean-toolchain-pin.sh*) exit 0 ;;
    esac
    exit "${NIX_STUB_DEVELOP_EXIT:-0}"
    ;;
  *)
    echo "stub nix: unhandled subcommand '${1:-}'" >&2
    exit 1
    ;;
esac
STUB
chmod +x "$bin/nix"

# Invoked by absolute path below (not a bare `bash`) so the stub PATH prepend can never
# accidentally shadow the interpreter itself.
real_bash="$(command -v bash)"

failures=0
case_num=0

# run_case NAME "ENV1=v1 ENV2=v2 ..." "arg1 arg2 ..." STDIN WANT_EXIT WANT_TEXT WANT_DEVELOP
#   WANT_TEXT: a substring that must appear in combined stdout+stderr (empty to skip).
#   WANT_DEVELOP: a substring that must appear in develop-calls.log, or the literal "NONE" to
#     assert the log is empty (develop never invoked).
run_case() {
  local name="$1" envs="$2" args="$3" stdin="$4" want_exit="$5" want_text="$6" want_develop="$7"
  case_num=$((case_num + 1))
  local logdir="$work/log$case_num"
  mkdir -p "$logdir"
  : > "$logdir/develop-calls.log"
  : > "$logdir/build-calls.log"

  local out rc
  # shellcheck disable=SC2086
  out="$(cd "$tree" && env PATH="$bin:$PATH" NIX_STUB_LOG="$logdir" $envs \
    "$real_bash" full-gate.sh $args <<< "$stdin" 2>&1)"
  rc=$?

  local ok=1
  if [ "$rc" -ne "$want_exit" ]; then ok=0; fi
  if [ -n "$want_text" ] && ! grep -qF -- "$want_text" <<< "$out"; then ok=0; fi
  if [ "$want_develop" = "NONE" ]; then
    if [ -s "$logdir/develop-calls.log" ]; then ok=0; fi
  elif [ -n "$want_develop" ]; then
    grep -qF -- "$want_develop" "$logdir/develop-calls.log" || ok=0
  fi
  if grep -qi 'hacl\.cachix' <<< "$out"; then ok=0; fi
  if grep -qi 'hours' <<< "$out"; then ok=0; fi

  if [ "$ok" -eq 1 ]; then
    echo "[ok] $name (exit $rc)"
  else
    echo "[FAIL] $name: exit $rc (want $want_exit); develop.log:"
    sed 's/^/    develop: /' "$logdir/develop-calls.log"
    echo "  output:"
    sed 's/^/    /' <<< "$out"
    failures=$((failures + 1))
  fi
}

PIN_COMPLETE="nix/pin-complete.json"
PIN_NO_DARWIN="nix/pin-no-darwin.json"
PIN_DARWIN_BROKEN="nix/pin-darwin-broken.json"

# 1. Linux prebuilt, realized and fetch: x86_64-linux, complete pin -> step 1, .#extraction.
run_case "Linux prebuilt: dry-run reports the corrected prebuilt figures" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=prebuilt" \
  "--dry-run" "" 0 "shell: .#extraction" "NONE"

# 2. --source: non-TTY without --yes exits 2, develop never invoked.
run_case "--source without --yes in a non-interactive session exits 2" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=source" \
  "--source" "" 2 "needs --yes" "NONE"

# 2b. --source --yes: proceeds to the source route (dry-run: reports, never calls develop).
run_case "--source --yes proceeds to extraction-source" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=source" \
  "--source --yes --dry-run" "" 0 "shell: .#extraction-source" "NONE"

# 3. darwin with an asset (the current real case): aarch64-darwin, complete pin -> step 1.
run_case "aarch64-darwin with a prebuilt asset takes the prebuilt route" \
  "FULL_GATE_TEST_SYSTEM=aarch64-darwin FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=prebuilt" \
  "--dry-run" "" 0 "shell: .#extraction" "NONE"

# 4. darwin without an asset, not known broken: source prompt, decline falls back to .#build.
# NIX_STUB_DEVELOP_EXIT=3 mimics check.sh --committed-extraction's real INCOMPLETE exit code.
run_case "aarch64-darwin without an asset: declining the source prompt falls back to committed-extraction" \
  "FULL_GATE_TEST_SYSTEM=aarch64-darwin FULL_GATE_TEST_PIN=$PIN_NO_DARWIN FULL_GATE_TEST_BRIDGE_FETCHED=1 FULL_GATE_TEST_TTY=1 NIX_STUB_DRYRUN_MODE=empty NIX_STUB_DEVELOP_EXIT=3" \
  "" "n" 3 "committed-extraction" "committed-extraction"

# 4b. same, but accepting the source prompt takes .#extraction-source.
run_case "aarch64-darwin without an asset: accepting the source prompt takes extraction-source" \
  "FULL_GATE_TEST_SYSTEM=aarch64-darwin FULL_GATE_TEST_PIN=$PIN_NO_DARWIN FULL_GATE_TEST_BRIDGE_FETCHED=1 FULL_GATE_TEST_TTY=1 NIX_STUB_DRYRUN_MODE=source" \
  "" "y" 0 "" "extraction-source"

# 5. darwin known broken: skips the source prompt entirely, goes straight to .#build.
run_case "aarch64-darwin known-broken from-source: no prompt, straight to committed-extraction" \
  "FULL_GATE_TEST_SYSTEM=aarch64-darwin FULL_GATE_TEST_PIN=$PIN_DARWIN_BROKEN FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=empty NIX_STUB_DEVELOP_EXIT=3" \
  "" "" 3 "known-broken" "committed-extraction"

# 5b. x86_64-darwin: always step 3, even with the complete pin (no from-source route exists).
run_case "x86_64-darwin always takes committed-extraction (no from-source route)" \
  "FULL_GATE_TEST_SYSTEM=x86_64-darwin FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=empty NIX_STUB_DEVELOP_EXIT=3" \
  "" "" 3 "committed-extraction" "committed-extraction"

# 5c. x86_64-darwin: --source is refused outright (exit 2), develop never invoked.
run_case "x86_64-darwin refuses --source outright" \
  "FULL_GATE_TEST_SYSTEM=x86_64-darwin FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=empty" \
  "--source --yes" "" 2 "unavailable on x86_64-darwin" "NONE"

# 6. a failing dry-run: the probe itself fails, full-gate.sh exits 2, develop never invoked.
run_case "a failing probe (nix build --dry-run itself fails) exits 2, never calls develop" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=fail" \
  "--yes" "" 2 "probe" "NONE"

# 7. comparator/landrun under --recheck, --dry-run: PROBE_MINOR reported, never asked (dry-run
# never blocks on TTY), prebuilt route still taken.
run_case "comparator/landrun under --recheck: --dry-run reports without asking" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=minor" \
  "--recheck --dry-run" "" 0 "would ask to build Comparator/landrun locally" "NONE"

# 7b. comparator/landrun under --recheck: accepting the prompt keeps the prebuilt/recheck route.
run_case "comparator/landrun under --recheck: accepting the prompt keeps --recheck" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 FULL_GATE_TEST_TTY=1 NIX_STUB_DRYRUN_MODE=minor" \
  "--recheck" "y" 0 "running the gate in .#recheck" "framed_channel/check.sh --recheck"

# 7c. comparator/landrun under --recheck: declining drops --recheck and runs the plain gate, no
# --recheck reaching check.sh.
run_case "comparator/landrun under --recheck: declining drops --recheck, runs the plain gate" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 FULL_GATE_TEST_TTY=1 NIX_STUB_DRYRUN_MODE=minor" \
  "--recheck" "n" 0 "running the gate in .#extraction" "framed_channel/check.sh"

# 8. the bridge-fetch prompt: not fetched, non-TTY without --yes exits 2 (uniform consent rule).
run_case "the bridge-fetch prompt: non-TTY without --yes exits 2" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=0 NIX_STUB_DRYRUN_MODE=empty" \
  "" "" 2 "needs --yes" "NONE"

# 8b. the bridge-fetch prompt: --dry-run reports it without asking (dry-run never blocks on TTY).
run_case "the bridge-fetch prompt: --dry-run reports without asking" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=0 NIX_STUB_DRYRUN_MODE=empty" \
  "--dry-run" "" 0 "would also fetch: Aeneas/Mathlib" "NONE"

# 8c. the bridge-fetch prompt: declining falls back to the committed-extraction pre-check rather
# than silently fetching anyway (D1).
run_case "the bridge-fetch prompt: declining falls back to committed-extraction" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=0 FULL_GATE_TEST_TTY=1 NIX_STUB_DRYRUN_MODE=empty NIX_STUB_DEVELOP_EXIT=3" \
  "" "n" 3 "declined the bridge fetch; falling back to the committed-extraction pre-check" "committed-extraction"

# 8d. the bridge-fetch prompt: accepting proceeds to the normal (prebuilt) route.
run_case "the bridge-fetch prompt: accepting proceeds to the normal route" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=0 FULL_GATE_TEST_TTY=1 NIX_STUB_DRYRUN_MODE=empty" \
  "" "y" 0 "running the gate in .#extraction" "framed_channel/check.sh"

# 8c. no pass-through arguments at all: check.sh is invoked with nothing after its path. This is
# the zero-length `check_args` expansion, which under `set -u` is an unbound-variable error on
# bash < 4.4 unless written `${arr[@]+"${arr[@]}"}` (tests/launcher-compat/run.sh runs the same
# launcher under the host /bin/bash; this case pins the argument vector itself).
run_case "no pass-through arguments: check.sh runs with an empty argument vector" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=empty" \
  "--yes" "" 0 "running the gate in .#extraction" "framed_channel/check.sh"
run_case "no pass-through arguments under --recheck: exactly --recheck reaches check.sh" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=empty" \
  "--recheck --yes" "" 0 "running the gate in .#recheck" "framed_channel/check.sh --recheck"

# 8d. pass-through arguments survive verbatim, after --recheck when both are present.
run_case "pass-through arguments after -- reach check.sh verbatim" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE FULL_GATE_TEST_BRIDGE_FETCHED=1 NIX_STUB_DRYRUN_MODE=empty" \
  "--recheck --yes -- --clean --lean-only" "" 0 "" "framed_channel/check.sh --recheck --clean --lean-only"

# --support-level: route/gate/recheck resolution across all four designated systems. Never
# touches the stub nix at all (exits before the probe), so every case asserts want_develop=NONE
# and needs no NIX_STUB_DRYRUN_MODE.

# 9. x86_64-linux, complete pin: full gate, complete recheck, prebuilt route.
run_case "--support-level: x86_64-linux resolves prebuilt/full/complete" \
  "FULL_GATE_TEST_SYSTEM=x86_64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE" \
  "--support-level" "" 0 "route=prebuilt" "NONE"

# 10. aarch64-linux, complete pin: same shape as x86_64-linux (both hasComparator systems).
run_case "--support-level: aarch64-linux resolves prebuilt/full/complete" \
  "FULL_GATE_TEST_SYSTEM=aarch64-linux FULL_GATE_TEST_PIN=$PIN_COMPLETE" \
  "--support-level" "" 0 "recheck=complete" "NONE"

# 11. aarch64-darwin, complete pin (has a darwin asset): prebuilt route, but recheck degrades to
# partial -- devShells.aarch64-darwin.recheck exists (defined unconditionally) but drops
# Comparator (hasComparator is Linux-only), per the plan's verified-mechanism correction.
run_case "--support-level: aarch64-darwin with an asset resolves prebuilt/full/partial" \
  "FULL_GATE_TEST_SYSTEM=aarch64-darwin FULL_GATE_TEST_PIN=$PIN_COMPLETE" \
  "--support-level" "" 0 "recheck=partial" "NONE"

# 12. aarch64-darwin, no darwin asset (macos_fallback: true), not known-broken: the fallback
# chain's middle rung -- consented from-source route -- gate stays "full" (the fallback chain
# itself is still the full-gate path), recheck unavailable.
run_case "--support-level: aarch64-darwin without an asset resolves source/full/unavailable, reports macos_fallback" \
  "FULL_GATE_TEST_SYSTEM=aarch64-darwin FULL_GATE_TEST_PIN=$PIN_NO_DARWIN" \
  "--support-level" "" 0 "route=source" "NONE"
run_case "--support-level: aarch64-darwin without an asset reports macos_fallback=true" \
  "FULL_GATE_TEST_SYSTEM=aarch64-darwin FULL_GATE_TEST_PIN=$PIN_NO_DARWIN" \
  "--support-level" "" 0 "macos_fallback=true" "NONE"

# 13. aarch64-darwin, darwin from-source known-broken: the fallback chain's last rung --
# committed-extraction -- gate is still "full" (has_aeneas_source is true; only the *current*
# route degraded), recheck unavailable.
run_case "--support-level: aarch64-darwin known-broken resolves committed-extraction/full/unavailable" \
  "FULL_GATE_TEST_SYSTEM=aarch64-darwin FULL_GATE_TEST_PIN=$PIN_DARWIN_BROKEN" \
  "--support-level" "" 0 "route=committed-extraction" "NONE"

# 14. x86_64-darwin: always committed-extraction/light-only, regardless of pin completeness --
# no from-source route exists there at all (has_aeneas_source is false).
run_case "--support-level: x86_64-darwin resolves committed-extraction/light-only, no prompt" \
  "FULL_GATE_TEST_SYSTEM=x86_64-darwin FULL_GATE_TEST_PIN=$PIN_COMPLETE" \
  "--support-level" "" 0 "gate=light-only" "NONE"

# 15. --support-level never asks and never exits non-zero, even fully non-interactive (no TTY,
# no --yes) and even on the system with the narrowest support (x86_64-darwin).
run_case "--support-level never prompts and always exits 0 (no --yes, no TTY)" \
  "FULL_GATE_TEST_SYSTEM=x86_64-darwin FULL_GATE_TEST_PIN=$PIN_COMPLETE" \
  "--support-level" "" 0 "system=x86_64-darwin" "NONE"

if [ $failures -ne 0 ]; then
  echo "tests/full-gate: $failures of $case_num case(s) failed"
  exit 1
fi
echo "tests/full-gate: all $case_num cases pass"
