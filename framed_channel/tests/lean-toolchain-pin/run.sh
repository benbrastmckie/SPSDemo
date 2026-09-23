#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/lean-toolchain-pin/run.sh -- fixture tests for ../../nix/lean-toolchain-pin.sh.
#
# Drives the script entirely through its LEAN_TOOLCHAIN_PIN_TEST_* hooks (see the script's own
# header): a matching digest, a mismatching digest, a pin/lean-toolchain inconsistency, an
# unknown system, --check-consistency-only, and a missing required tool (jq). No real network
# call.
#
# Usage: bash tests/lean-toolchain-pin/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, jq, coreutils (sha256sum).
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
SCRIPT="$EX/../nix/lean-toolchain-pin.sh"

command -v jq > /dev/null 2>&1 || { echo "tests/lean-toolchain-pin: jq is not on PATH; run inside nix develop" >&2; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

failures=0
case_num=0

# path_without CMD -- the current $PATH with every directory that contains an executable CMD
# removed (same technique as tests/recheck-revs/run.sh's path_without_jq).
path_without() {
  local cmd="$1" IFS=':' dir out=()
  for dir in $PATH; do
    [ -x "$dir/$cmd" ] && continue
    out+=("$dir")
  done
  local joined
  joined="$(IFS=:; echo "${out[*]}")"
  printf '%s' "$joined"
}

# write_toolchain_files DIR CONTENTS... -- writes len(CONTENTS) lean-toolchain-like files under
# DIR/tc1, DIR/tc2, ... and prints the space-separated list of their paths.
write_toolchain_files() {
  local d="$1"; shift
  local i=0 paths=""
  for c in "$@"; do
    i=$((i + 1))
    printf '%s\n' "$c" > "$d/tc$i"
    paths="$paths $d/tc$i"
  done
  printf '%s' "$paths"
}

expect() {
  # expect NAME WANT_RC WANT_TEXT ENV_ASSIGNMENTS... -- ARGS...   (ARGS... may be empty)
  local name="$1" want_rc="$2" want_text="$3"
  shift 3
  local env_args=()
  while [ "$1" != "--" ]; do env_args+=("$1"); shift; done
  shift
  case_num=$((case_num + 1))
  local out rc
  out="$(env "${env_args[@]}" bash "$SCRIPT" "$@" 2>&1)"
  rc=$?
  if [ "$rc" -eq "$want_rc" ] && { [ -z "$want_text" ] || grep -qF -- "$want_text" <<< "$out"; }; then
    echo "[ok] $name (exit $rc)"
  else
    echo "[FAIL] $name: exit $rc (expected $want_rc), text '$want_text'"
    sed 's/^/    /' <<< "$out"
    failures=$((failures + 1))
  fi
}

# ---- fixture data -------------------------------------------------------------------------
d="$work/consistent"
mkdir -p "$d"
tc_files="$(write_toolchain_files "$d" "leanprover/lean4:v4.31.0" "leanprover/lean4:v4.31.0" "leanprover/lean4:v4.31.0")"

d2="$work/inconsistent"
mkdir -p "$d2"
tc_files_bad="$(write_toolchain_files "$d2" "leanprover/lean4:v4.31.0" "leanprover/lean4:v4.30.0" "leanprover/lean4:v4.31.0")"

asset_file="$work/asset.bin"
printf 'a fixture lean release asset, not the real bytes\n' > "$asset_file"
asset_sha="$(sha256sum "$asset_file" | cut -d' ' -f1)"

pin="$work/pin.json"
jq -n --arg sha "$asset_sha" '{
  lean_toolchain: "leanprover/lean4:v4.31.0",
  assets: { "x86_64-linux": { name: "asset.bin", sha256: $sha } }
}' > "$pin"

pin_no_assets="$work/pin-no-assets.json"
jq -n '{ lean_toolchain: "leanprover/lean4:v4.31.0", assets: {} }' > "$pin_no_assets"

# ---- cases ---------------------------------------------------------------------------------

expect "matching digest, verified" 0 "verified asset.bin for x86_64-linux" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin" LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES="$tc_files" \
  LEAN_TOOLCHAIN_PIN_TEST_SYSTEM="x86_64-linux" LEAN_TOOLCHAIN_PIN_TEST_FILE="$asset_file" \
  --

expect "mismatching digest fails" 1 "sha256 mismatch" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin" LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES="$tc_files" \
  LEAN_TOOLCHAIN_PIN_TEST_SYSTEM="x86_64-linux" LEAN_TOOLCHAIN_PIN_TEST_FILE="$EX/README.md" \
  --

expect "pin/lean-toolchain inconsistency fails" 1 "does not match" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin" LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES="$tc_files_bad" \
  LEAN_TOOLCHAIN_PIN_TEST_SYSTEM="x86_64-linux" LEAN_TOOLCHAIN_PIN_TEST_FILE="$asset_file" \
  --

expect "unknown system, no pin, exits 0" 0 "no pin for this system" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin" LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES="$tc_files" \
  LEAN_TOOLCHAIN_PIN_TEST_SYSTEM="riscv64-linux" \
  --

expect "pin with no assets at all, exits 0" 0 "no pin for this system" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin_no_assets" LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES="$tc_files" \
  LEAN_TOOLCHAIN_PIN_TEST_SYSTEM="x86_64-linux" \
  --

expect "--check-consistency-only, consistent, no network" 0 "no network" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin" LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES="$tc_files" \
  -- --check-consistency-only

expect "--check-consistency-only, inconsistent, still fails" 1 "does not match" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin" LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES="$tc_files_bad" \
  -- --check-consistency-only

malformed_pin="$work/malformed.json"
jq -n '{ assets: {} }' > "$malformed_pin"
expect "malformed pin (.lean_toolchain absent)" 2 "has no .lean_toolchain" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$malformed_pin" \
  --

expect "missing lean-toolchain file" 2 "lean-toolchain file not found" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin" LEAN_TOOLCHAIN_PIN_TEST_TOOLCHAIN_FILES="$work/does-not-exist" \
  -- --check-consistency-only

expect "missing pin file" 2 "pin file not found" \
  LEAN_TOOLCHAIN_PIN_TEST_PIN="$work/no-such-pin.json" \
  --

expect "--help" 0 "Usage: bash nix/lean-toolchain-pin.sh" \
  -- --help

expect "unknown argument" 2 "unknown argument" \
  -- --bogus

# jq not on PATH (--help is parsed before the jq check and would still succeed, so this uses a
# non-help invocation).
case_num=$((case_num + 1))
out="$(env LEAN_TOOLCHAIN_PIN_TEST_PIN="$pin" PATH="$(path_without jq)" bash "$SCRIPT" 2>&1)"
rc=$?
if [ "$rc" -eq 2 ] && grep -qF -- "jq is required" <<< "$out"; then
  echo "[ok] jq not on PATH (exit $rc)"
else
  echo "[FAIL] jq not on PATH: exit $rc, text '$out'"
  failures=$((failures + 1))
fi

# A "neither sha256sum nor shasum on PATH" case is not exercised here: on this development
# sandbox coreutils (sha256sum, tr, dirname, cut, ...) all live in one PATH directory, so
# removing it the same way path_without() removes jq's also removes tools the script needs
# before it ever reaches sha256_of (dirname, tr), which would test a PATH layout artifact of
# this sandbox rather than the script's own sha256_of fallback. The fallback itself
# (command -v sha256sum, else command -v shasum, else exit 2) is the same shape as the jq check
# directly above, which the "jq not on PATH" case does exercise end to end.

if [ "$failures" -eq 0 ]; then
  echo "lean-toolchain-pin: PASS ($case_num cases)"
  exit 0
fi
echo "lean-toolchain-pin: FAIL ($failures/$case_num case(s))"
exit 1
