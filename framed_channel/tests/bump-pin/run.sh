#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/bump-pin/run.sh -- fixture tests for nix/bump-aeneas-pin.sh's middle-rule (30-day cap)
# selection algorithm, without ever calling a real `gh`, `nix`, `lake`, `tar` or `git`.
#
# Drives the real script through its BUMP_PIN_TEST_* hooks (see the script's own header comment):
# a stub releases list, stub commit dates (exercising the created_at fallback), a stub "bundle"
# (lean-toolchain/charon/rust-nightly/digest/darwin-job read), and a stub gate verdict per
# candidate tag. BUMP_PIN_TEST_SKIP_GIT=1 throughout (no real repo here) and
# BUMP_PIN_TEST_APPLY_LOG records every "would-apply" call instead of invoking nix/lake for real,
# so a case can assert exactly which candidates were actually applied+gated (only those cost a
# unit of --max-gates) versus merely classified and rejected before ever reaching the gate.
#
# Usage: bash tests/bump-pin/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, jq.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

if ! command -v jq > /dev/null 2>&1; then
  echo "tests/bump-pin: jq is not on PATH; run inside nix develop" >&2
  exit 2
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
SCRIPT="$EX/../nix/bump-aeneas-pin.sh"
[ -f "$SCRIPT" ] || { echo "tests/bump-pin: nix/bump-aeneas-pin.sh not found relative to the repository root" >&2; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

real_bash="$(command -v bash)"
LEAN="leanprover/lean4:v4.31.0"

failures=0
case_num=0

ASSET_LINUX_ONLY='{"x86_64-linux":{"name":"aeneas-linux-x86_64.tar.gz","sha256":"sha256-aaaa"},"aarch64-linux":{"name":"aeneas-linux-aarch64.tar.gz","sha256":"sha256-bbbb"}}'
ASSET_ALL='{"x86_64-linux":{"name":"aeneas-linux-x86_64.tar.gz","sha256":"sha256-cccc"},"aarch64-linux":{"name":"aeneas-linux-aarch64.tar.gz","sha256":"sha256-dddd"},"aarch64-darwin":{"name":"aeneas-macos-aarch64.tar.gz","sha256":"sha256-eeee"}}'

# run_case NAME ENV_SETUP_FN WANT_EXIT JQ_ASSERT WANT_STDERR
#   ENV_SETUP_FN: a function name that populates $cdir with releases.json/commit-dates.json/
#     bundle.json/gate.json/pin.json and echoes the extra `KEY=VALUE` env assignments (space
#     separated) this case needs beyond the common set (BUMP_PIN_TEST_*, always wired below).
#   JQ_ASSERT: a jq boolean expression evaluated against the captured stdout JSON (the script's
#     final summary line), or empty to skip. "true" literal also allowed.
#   WANT_STDERR: a substring that must appear on stderr, or empty to skip.
run_case() {
  local name="$1" setup_fn="$2" args="$3" want_exit="$4" jq_assert="$5" want_stderr="$6"
  case_num=$((case_num + 1))
  local cdir="$work/case$case_num"
  mkdir -p "$cdir"
  "$setup_fn" "$cdir"

  local applylog="$cdir/apply.log"
  : > "$applylog"

  local out err rc
  out="$(cd "$cdir" && env \
      BUMP_PIN_TEST_RELEASES_JSON="$cdir/releases.json" \
      BUMP_PIN_TEST_COMMIT_DATES_JSON="$cdir/commit-dates.json" \
      BUMP_PIN_TEST_BUNDLE_JSON="$cdir/bundle.json" \
      BUMP_PIN_TEST_GATE_JSON="$cdir/gate.json" \
      BUMP_PIN_TEST_PIN_FILE="$cdir/pin.json" \
      BUMP_PIN_TEST_LEAN_TOOLCHAIN="$LEAN" \
      BUMP_PIN_TEST_APPLY_LOG="$applylog" \
      BUMP_PIN_TEST_SKIP_GIT=1 \
      "$real_bash" "$SCRIPT" $args 2> "$cdir/stderr.log")"
  rc=$?
  err="$(cat "$cdir/stderr.log")"

  local ok=1
  if [ "$rc" -ne "$want_exit" ]; then ok=0; fi
  if [ -n "$jq_assert" ] && [ "$jq_assert" != true ]; then
    if ! echo "$out" | jq -e "$jq_assert" > /dev/null 2>&1; then ok=0; fi
  fi
  if [ -n "$want_stderr" ] && ! grep -qF -- "$want_stderr" <<< "$err"; then ok=0; fi

  if [ "$ok" -eq 1 ]; then
    echo "[ok] $name (exit $rc)"
  else
    echo "[FAIL] $name: exit $rc (want $want_exit)"
    echo "  stdout: $out"
    echo "  stderr:"; sed 's/^/    /' <<< "$err"
    echo "  apply.log:"; sed 's/^/    /' "$applylog"
    failures=$((failures + 1))
  fi
  # LAST_DIR is exported for a case's own post-hoc assertions (apply.log contents, pin-file bytes).
  LAST_DIR="$cdir"
}

# assert_extra NAME CONDITION_DESC bash-boolean-expression(as a command)
assert_extra() {
  local name="$1" desc="$2"
  shift 2
  if "$@"; then
    echo "[ok] $name: $desc"
  else
    echo "[FAIL] $name: $desc"
    failures=$((failures + 1))
  fi
}

# ============================================================================ case 1
# complete branch: L (227f4e7-like) lacks darwin; C one day older is complete and passes -> C
# selected, macos_fallback false (the real Phase 4 case).
setup_case1() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.09.19-227f4e7", created_at:"2026-09-19T17:20:51Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]},
    {tag_name:"nightly-2026.09.17-86158eb", created_at:"2026-09-17T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/5"}]}
  ]' > "$d/releases.json"
  jq -n '{
    "227f4e7": {commit_date:"2026-09-17T17:20:51Z", full_sha:"227f4e7f00000000000000000000000000000f"},
    "86158eb": {commit_date:"2026-09-16T14:10:22Z", full_sha:"86158eb200000000000000000000000000000e"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" --argjson all "$ASSET_ALL" '{
    "nightly-2026.09.19-227f4e7": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"2026-09-17", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.09.17-86158eb": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c2", charon_pin:"c2", rust_nightly:"2026-08-18", digest_ok:true, assets:$all, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.09.19-227f4e7":"pass","nightly-2026.09.17-86158eb":"pass"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "complete branch: newer Linux-complete-only L, one-day-older complete C -> C wins" \
  setup_case1 "" 0 '.selected.tag=="nightly-2026.09.17-86158eb" and .branch=="complete" and .macos_fallback==false' ""
assert_extra "case1 pin file" "written pin.rev equals C's full sha" \
  bash -c "[ \"\$(jq -r .rev "$LAST_DIR/pin.json")\" = 86158eb200000000000000000000000000000e ]"

# ============================================================================ case 2
# Linux-complete branch: the only passing C is 31 days older than L -> L selected,
# macos_fallback true, reason window-exhausted; C must never be gated (never in apply.log).
setup_case2() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.10.01-lll1111", created_at:"2026-10-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]},
    {tag_name:"nightly-2026.08.31-ccc2222", created_at:"2026-08-31T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/5"}]}
  ]' > "$d/releases.json"
  jq -n '{
    "lll1111": {commit_date:"2026-10-01T00:00:00Z", full_sha:"lll1111100000000000000000000000000000f"},
    "ccc2222": {commit_date:"2026-08-31T00:00:00Z", full_sha:"ccc2222200000000000000000000000000000e"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" --argjson all "$ASSET_ALL" '{
    "nightly-2026.10.01-lll1111": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.08.31-ccc2222": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c2", charon_pin:"c2", rust_nightly:"r2", digest_ok:true, assets:$all, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.10.01-lll1111":"pass","nightly-2026.08.31-ccc2222":"fail"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "Linux-complete branch: only passing C is 31d older -> L wins, window-exhausted" \
  setup_case2 "" 0 '.selected.tag=="nightly-2026.10.01-lll1111" and .branch=="linux-complete" and .macos_fallback==true and .reason=="window-exhausted"' ""
assert_extra "case2 no C gate" "ccc2222 full sha never applied (outside window, never gated)" \
  bash -c "! grep -q ccc2222 '$LAST_DIR/apply.log'"

# ============================================================================ case 3
# boundary: C 29d older and exactly 30d older are selected; C 30d+1s older is not.
setup_case3_boundary() {
  local d="$1" c_date="$2"
  jq -n --arg cd "$c_date" '[
    {tag_name:"nightly-2026.10.01-lll1111", created_at:"2026-10-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]},
    {tag_name:"nightly-2026.09.01-ccc2222", created_at:$cd,
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/5"}]}
  ]' > "$d/releases.json"
  jq -n --arg cd "$c_date" '{
    "lll1111": {commit_date:"2026-10-01T00:00:00Z", full_sha:"lll1111100000000000000000000000000000f"},
    "ccc2222": {commit_date:$cd, full_sha:"ccc2222200000000000000000000000000000e"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" --argjson all "$ASSET_ALL" '{
    "nightly-2026.10.01-lll1111": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.09.01-ccc2222": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c2", charon_pin:"c2", rust_nightly:"r2", digest_ok:true, assets:$all, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.10.01-lll1111":"pass","nightly-2026.09.01-ccc2222":"pass"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
setup_case3a() { setup_case3_boundary "$1" "2026-09-02T00:00:00Z"; } # 29 days
setup_case3b() { setup_case3_boundary "$1" "2026-09-01T00:00:00Z"; } # exactly 30 days
setup_case3c() { setup_case3_boundary "$1" "2026-08-31T23:59:59Z"; } # 30 days + 1 second
run_case "boundary: C 29 days older is selected" setup_case3a "" 0 '.selected.tag=="nightly-2026.09.01-ccc2222"' ""
run_case "boundary: C exactly 30 days older is selected (inclusive)" setup_case3b "" 0 '.selected.tag=="nightly-2026.09.01-ccc2222"' ""
run_case "boundary: C 30 days + 1 second older is NOT selected" setup_case3c "" 0 '.selected.tag=="nightly-2026.10.01-lll1111" and .reason=="window-exhausted"' ""

# ============================================================================ case 4
# L itself complete: L selected, no window search (an older complete candidate is never gated).
setup_case4() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.10.01-lll1111", created_at:"2026-10-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/6"}]},
    {tag_name:"nightly-2026.09.01-ooo3333", created_at:"2026-09-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/5"}]}
  ]' > "$d/releases.json"
  jq -n '{
    "lll1111": {commit_date:"2026-10-01T00:00:00Z", full_sha:"lll1111100000000000000000000000000000f"},
    "ooo3333": {commit_date:"2026-09-01T00:00:00Z", full_sha:"ooo3333300000000000000000000000000000e"}
  }' > "$d/commit-dates.json"
  jq -n --argjson all "$ASSET_ALL" '{
    "nightly-2026.10.01-lll1111": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$all, darwin_job_failed:false},
    "nightly-2026.09.01-ooo3333": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c2", charon_pin:"c2", rust_nightly:"r2", digest_ok:true, assets:$all, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.10.01-lll1111":"pass","nightly-2026.09.01-ooo3333":"pass"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "L itself complete: selected directly, no window search" \
  setup_case4 "" 0 '.selected.tag=="nightly-2026.10.01-lll1111" and .branch=="complete" and .C==null' ""
assert_extra "case4 no window search" "the older complete candidate is never applied" \
  bash -c "! grep -q ooo3333 '$LAST_DIR/apply.log'"

# ============================================================================ case 5
# a failing gate on C moves to the next complete candidate in the window; a --max-gates cut sets
# budget-truncated.
setup_case5() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.10.01-lll1111", created_at:"2026-10-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]},
    {tag_name:"nightly-2026.09.25-ccc0001", created_at:"2026-09-25T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/5"}]},
    {tag_name:"nightly-2026.09.20-ccc0002", created_at:"2026-09-20T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/6"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/7"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/8"}]}
  ]' > "$d/releases.json"
  jq -n '{
    "lll1111": {commit_date:"2026-10-01T00:00:00Z", full_sha:"lll1111100000000000000000000000000000f"},
    "ccc0001": {commit_date:"2026-09-25T00:00:00Z", full_sha:"ccc0001100000000000000000000000000000e"},
    "ccc0002": {commit_date:"2026-09-20T00:00:00Z", full_sha:"ccc0002200000000000000000000000000000d"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" --argjson all "$ASSET_ALL" '{
    "nightly-2026.10.01-lll1111": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.09.25-ccc0001": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c2", charon_pin:"c2", rust_nightly:"r2", digest_ok:true, assets:$all, darwin_job_failed:false},
    "nightly-2026.09.20-ccc0002": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c3", charon_pin:"c3", rust_nightly:"r3", digest_ok:true, assets:$all, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.10.01-lll1111":"pass","nightly-2026.09.25-ccc0001":"fail","nightly-2026.09.20-ccc0002":"pass"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "a failing gate on C moves to the next complete candidate in the window" \
  setup_case5 "--max-gates 4" 0 \
  '.selected.tag=="nightly-2026.09.20-ccc0002" and .branch=="complete" and .gate_failures==[{"tag":"nightly-2026.09.25-ccc0001","stage":"test-hook"}]' ""
assert_extra "case5 pin file" "final pin.rev is the second (passing) C, not the first (failing) one" \
  bash -c "[ \"\$(jq -r .rev "$LAST_DIR/pin.json")\" = ccc0002200000000000000000000000000000d ]"
run_case "a --max-gates cut before C is reached reports budget-truncated" \
  setup_case5 "--max-gates 1" 0 '.selected.tag=="nightly-2026.10.01-lll1111" and .reason=="budget-truncated"' ""

# ============================================================================ case 6
# a newer release missing aeneas-linux-aarch64 is never L (excluded from the Linux-complete
# search entirely, never gated) -- and a darwin-only gap (case 1's L) never blocks Linux.
setup_case6() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.10.05-rrr0000", created_at:"2026-10-05T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/0"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/0b"}]},
    {tag_name:"nightly-2026.10.01-lll1111", created_at:"2026-10-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]}
  ]' > "$d/releases.json"
  jq -n '{
    "rrr0000": {commit_date:"2026-10-05T00:00:00Z", full_sha:"rrr0000000000000000000000000000000000f"},
    "lll1111": {commit_date:"2026-10-01T00:00:00Z", full_sha:"lll1111100000000000000000000000000000f"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" '{
    "nightly-2026.10.05-rrr0000": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c0", charon_pin:"c0", rust_nightly:"r0", digest_ok:true, assets:{}, darwin_job_failed:false},
    "nightly-2026.10.01-lll1111": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$linux, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.10.05-rrr0000":"pass","nightly-2026.10.01-lll1111":"pass"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "a release missing aarch64-linux is never L" \
  setup_case6 "" 0 '.selected.tag=="nightly-2026.10.01-lll1111"' ""
assert_extra "case6 x86+darwin-only release excluded" "rrr0000 (no aarch64-linux) never applied" \
  bash -c "! grep -q rrr0000 '$LAST_DIR/apply.log'"

# ============================================================================ case 7
# a Lean-toolchain change makes a candidate ineligible (no gate spent), and the search continues.
setup_case7() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.10.05-nnn0000", created_at:"2026-10-05T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]},
    {tag_name:"nightly-2026.10.01-lll1111", created_at:"2026-10-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"}]}
  ]' > "$d/releases.json"
  jq -n '{
    "nnn0000": {commit_date:"2026-10-05T00:00:00Z", full_sha:"nnn0000000000000000000000000000000000f"},
    "lll1111": {commit_date:"2026-10-01T00:00:00Z", full_sha:"lll1111100000000000000000000000000000f"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" '{
    "nightly-2026.10.05-nnn0000": {lean_toolchain:"leanprover/lean4:v4.30.0", charon_rev:"c0", charon_pin:"c0", rust_nightly:"r0", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.10.01-lll1111": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$linux, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.10.05-nnn0000":"pass","nightly-2026.10.01-lll1111":"pass"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "a Lean-toolchain mismatch makes a candidate ineligible; the search continues" \
  setup_case7 "" 0 '.selected.tag=="nightly-2026.10.01-lll1111"' "Lean bump available at nightly-2026.10.05-nnn0000: manual task"
assert_extra "case7 no gate spent" "the ineligible candidate is never applied" \
  bash -c "! grep -q nnn0000 '$LAST_DIR/apply.log'"

# ============================================================================ case 8
# a digest mismatch rejects the candidate (no gate spent); the search continues.
setup_case8() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.10.05-ddd0000", created_at:"2026-10-05T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]},
    {tag_name:"nightly-2026.10.01-lll1111", created_at:"2026-10-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"}]}
  ]' > "$d/releases.json"
  jq -n '{
    "ddd0000": {commit_date:"2026-10-05T00:00:00Z", full_sha:"ddd0000000000000000000000000000000000f"},
    "lll1111": {commit_date:"2026-10-01T00:00:00Z", full_sha:"lll1111100000000000000000000000000000f"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" '{
    "nightly-2026.10.05-ddd0000": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c0", charon_pin:"c0", rust_nightly:"r0", digest_ok:false, assets:$linux, darwin_job_failed:false},
    "nightly-2026.10.01-lll1111": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$linux, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.10.05-ddd0000":"pass","nightly-2026.10.01-lll1111":"pass"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "a digest mismatch rejects the candidate; the search continues" \
  setup_case8 "" 0 '.selected.tag=="nightly-2026.10.01-lll1111"' "candidate nightly-2026.10.05-ddd0000 rejected: asset digest mismatch"
assert_extra "case8 no gate spent" "the digest-mismatched candidate is never applied" \
  bash -c "! grep -q ddd0000 '$LAST_DIR/apply.log'"

# ============================================================================ case 9
# re-tagged commits collapse (keeping the newest tag); the commit date (not the tag date) drives
# the window; the created_at fallback is exercised and reported.
setup_case9() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.09.15-abc1234", created_at:"2026-09-15T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]},
    {tag_name:"nightly-2026.09.10-abc1234", created_at:"2026-09-10T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1b"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2b"}]},
    {tag_name:"nightly-2026.08.20-def9999", created_at:"2026-08-20T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"}]},
    {tag_name:"nightly-2026.07.26-cde5678", created_at:"2026-07-26T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/5"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/6"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/7"}]}
  ]' > "$d/releases.json"
  # def9999's commit_date is deliberately absent -> exercises the created_at fallback.
  jq -n '{
    "abc1234": {commit_date:"2026-09-15T00:00:00Z", full_sha:"abc1234400000000000000000000000000000f"},
    "cde5678": {commit_date:"2026-07-26T00:00:00Z", full_sha:"cde5678800000000000000000000000000000e"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" --argjson all "$ASSET_ALL" '{
    "nightly-2026.09.15-abc1234": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c0", charon_pin:"c0", rust_nightly:"r0", digest_ok:false, assets:$linux, darwin_job_failed:false},
    "nightly-2026.09.10-abc1234": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c0b", charon_pin:"c0b", rust_nightly:"r0b", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.08.20-def9999": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.07.26-cde5678": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c2", charon_pin:"c2", rust_nightly:"r2", digest_ok:true, assets:$all, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{
    "nightly-2026.09.15-abc1234":"pass","nightly-2026.09.10-abc1234":"pass",
    "nightly-2026.08.20-def9999":"pass","nightly-2026.07.26-cde5678":"pass"
  }' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "re-tag collapse keeps the newest tag; commit date (with created_at fallback) drives the window" \
  setup_case9 "" 0 \
  '.L.tag=="nightly-2026.08.20-def9999" and .selected.tag=="nightly-2026.07.26-cde5678" and (.commit_date_fallback_used | index("def9999") != null)' \
  ""
assert_extra "case9 collapse" "the older duplicate tag (09.10-abc1234) is never applied" \
  bash -c "! grep -q 'nightly-2026.09.10-abc1234' '$LAST_DIR/apply.log'"

# ============================================================================ case 10
# already current: writes nothing. A backward move reports direction backward.
setup_case10_already_current() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.09.17-86158eb", created_at:"2026-09-17T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/3"}]}
  ]' > "$d/releases.json"
  jq -n '{"86158eb": {commit_date:"2026-09-16T14:10:22Z", full_sha:"86158eb200000000000000000000000000000e"}}' > "$d/commit-dates.json"
  jq -n --argjson all "$ASSET_ALL" '{"nightly-2026.09.17-86158eb": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$all, darwin_job_failed:false}}' > "$d/bundle.json"
  jq -n '{"nightly-2026.09.17-86158eb":"pass"}' > "$d/gate.json"
  jq -n '{rev:"86158eb200000000000000000000000000000e", commit_date:"2026-09-16T14:10:22Z"}' > "$d/pin.json"
}
run_case "already current: writes nothing" \
  setup_case10_already_current "" 0 '.already_current==true' ""
assert_extra "case10 pin file untouched" "pin.json bytes are unchanged" \
  bash -c "[ \"\$(jq -c . "$LAST_DIR/pin.json")\" = '{\"rev\":\"86158eb200000000000000000000000000000e\",\"commit_date\":\"2026-09-16T14:10:22Z\"}' ]"
assert_extra "case10 no gate spent" "the already-current candidate is never applied" \
  bash -c "[ ! -s '$LAST_DIR/apply.log' ]"

setup_case10_backward() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.09.17-86158eb", created_at:"2026-09-17T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/3"}]}
  ]' > "$d/releases.json"
  jq -n '{"86158eb": {commit_date:"2026-09-16T14:10:22Z", full_sha:"86158eb200000000000000000000000000000e"}}' > "$d/commit-dates.json"
  jq -n --argjson all "$ASSET_ALL" '{"nightly-2026.09.17-86158eb": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$all, darwin_job_failed:false}}' > "$d/bundle.json"
  jq -n '{"nightly-2026.09.17-86158eb":"pass"}' > "$d/gate.json"
  # Current pin is NEWER (commit_date in December) than the only available candidate -> backward.
  jq -n '{rev:"newerrev0000000000000000000000000000000", commit_date:"2026-12-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "a backward move (selected older than current) reports direction backward" \
  setup_case10_backward "" 0 '.direction=="backward" and .distance_days > 0' ""

# ============================================================================ case 11
# --check-only writes nothing.
run_case "--check-only writes nothing (pin.json byte-identical before/after)" \
  setup_case1 "--check-only" 0 '.selected.tag=="nightly-2026.09.17-86158eb"' ""
assert_extra "case11 pin file untouched" "pin.json bytes are unchanged under --check-only" \
  bash -c "[ \"\$(jq -r .rev "$LAST_DIR/pin.json")\" = oldrev00000000000000000000000000000000 ]"
assert_extra "case11 no apply log" "nothing is applied under --check-only" \
  bash -c "[ ! -s '$LAST_DIR/apply.log' ]"

# ============================================================================ case 12
# charon-pin eligibility. The newest candidate's bundled charon disagrees with that candidate's
# own upstream charon-pin (an internally inconsistent release); the next one's charon-pin is
# unreadable (fail closed); the third agrees and is selected. Neither rejected candidate is ever
# applied or costs a gate.
setup_case12() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.10.05-ppp0000", created_at:"2026-10-05T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"}]},
    {tag_name:"nightly-2026.10.03-qqq0000", created_at:"2026-10-03T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/3"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/4"}]},
    {tag_name:"nightly-2026.10.01-lll1111", created_at:"2026-10-01T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/5"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/6"}]}
  ]' > "$d/releases.json"
  jq -n '{
    "ppp0000": {commit_date:"2026-10-05T00:00:00Z", full_sha:"ppp0000000000000000000000000000000000f"},
    "qqq0000": {commit_date:"2026-10-03T00:00:00Z", full_sha:"qqq0000000000000000000000000000000000f"},
    "lll1111": {commit_date:"2026-10-01T00:00:00Z", full_sha:"lll1111100000000000000000000000000000f"}
  }' > "$d/commit-dates.json"
  jq -n --argjson linux "$ASSET_LINUX_ONLY" '{
    "nightly-2026.10.05-ppp0000": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c0", charon_pin:"c0-other", rust_nightly:"r0", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.10.03-qqq0000": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c9", rust_nightly:"r9", digest_ok:true, assets:$linux, darwin_job_failed:false},
    "nightly-2026.10.01-lll1111": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$linux, darwin_job_failed:false}
  }' > "$d/bundle.json"
  jq -n '{"nightly-2026.10.05-ppp0000":"pass","nightly-2026.10.03-qqq0000":"pass","nightly-2026.10.01-lll1111":"pass"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "a bundled charon disagreeing with the candidate's own charon-pin is ineligible; the search continues" \
  setup_case12 "" 0 '.selected.tag=="nightly-2026.10.01-lll1111"' \
  "candidate nightly-2026.10.05-ppp0000 rejected: bundled charon is 'c0', but its own charon-pin is c0-other"
assert_extra "case12 disagreeing candidate" "never applied" \
  bash -c "! grep -q ppp0000 '$LAST_DIR/apply.log'"
assert_extra "case12 unreadable charon-pin" "rejected with its own reason (fail closed)" \
  grep -qF "candidate nightly-2026.10.03-qqq0000 rejected: its upstream charon-pin could not be read" "$LAST_DIR/stderr.log"
assert_extra "case12 unreadable charon-pin" "never applied" \
  bash -c "! grep -q qqq0000 '$LAST_DIR/apply.log'"
assert_extra "case12 agreeing candidate" "is the one applied" \
  grep -q lll1111 "$LAST_DIR/apply.log"

# ============================================================================ case 13
# --dry-run is a synonym for --check-only: writes nothing (D4).
run_case "--dry-run writes nothing (pin.json byte-identical before/after)" \
  setup_case1 "--dry-run" 0 '.selected.tag=="nightly-2026.09.17-86158eb"' ""
assert_extra "case13 pin file untouched" "pin.json bytes are unchanged under --dry-run" \
  bash -c "[ \"\$(jq -r .rev "$LAST_DIR/pin.json")\" = oldrev00000000000000000000000000000000 ]"
assert_extra "case13 no apply log" "nothing is applied under --dry-run" \
  bash -c "[ ! -s '$LAST_DIR/apply.log' ]"

# ============================================================================ case 14
# --apply-ungated applies the selected candidate WITHOUT gating it (the old --dry-run behaviour,
# renamed -- D4). gate.json records "fail" for the only candidate: a real (ungated-off) run would
# never select it (the gate would reject it and the search would end "no candidate could be
# selected"), but --apply-ungated skips the gate entirely and applies it anyway.
setup_case14_apply_ungated() {
  local d="$1"
  jq -n '[
    {tag_name:"nightly-2026.09.17-86158eb", created_at:"2026-09-17T00:00:00Z",
     assets:[{name:"aeneas-linux-x86_64.tar.gz",digest:"",browser_download_url:"http://x/1"},
             {name:"aeneas-linux-aarch64.tar.gz",digest:"",browser_download_url:"http://x/2"},
             {name:"aeneas-macos-aarch64.tar.gz",digest:"",browser_download_url:"http://x/3"}]}
  ]' > "$d/releases.json"
  jq -n '{"86158eb": {commit_date:"2026-09-16T14:10:22Z", full_sha:"86158eb200000000000000000000000000000e"}}' > "$d/commit-dates.json"
  jq -n --argjson all "$ASSET_ALL" '{"nightly-2026.09.17-86158eb": {lean_toolchain:"leanprover/lean4:v4.31.0", charon_rev:"c1", charon_pin:"c1", rust_nightly:"r1", digest_ok:true, assets:$all, darwin_job_failed:false}}' > "$d/bundle.json"
  jq -n '{"nightly-2026.09.17-86158eb":"fail"}' > "$d/gate.json"
  jq -n '{rev:"oldrev00000000000000000000000000000000", commit_date:"2026-01-01T00:00:00Z"}' > "$d/pin.json"
}
run_case "--apply-ungated applies the selected candidate without gating it" \
  setup_case14_apply_ungated "--apply-ungated" 0 '.selected.tag=="nightly-2026.09.17-86158eb"' ""
assert_extra "case14 pin file written" "pin.rev equals the candidate's full sha, despite a failing gate" \
  bash -c "[ \"\$(jq -r .rev "$LAST_DIR/pin.json")\" = 86158eb200000000000000000000000000000e ]"
assert_extra "case14 apply log" "the candidate was applied" \
  grep -q 86158eb "$LAST_DIR/apply.log"
# Sanity check: the SAME setup, ungated off (no flag), never selects this candidate -- proves the
# gate is genuinely skipped only under --apply-ungated, not silently always-passing.
run_case "the same fixture, real mode: a failing gate means no candidate is selected" \
  setup_case14_apply_ungated "" 1 \
  '.gate_failures==[{"tag":"nightly-2026.09.17-86158eb","stage":"test-hook"}]' \
  "no Linux-complete eligible candidate passed the gate"

# ============================================================================ case 15
# run_gate_real invokes check.sh --skip-approvals: the test hooks bypass run_gate_real entirely
# (gate_pass short-circuits to BUMP_PIN_TEST_GATE_JSON), so this is a static, grep-based assertion
# over the function body rather than an exercised run.
assert_extra "run_gate_real calls check.sh --skip-approvals" \
  "static: the search gate never runs the approvals stage (candidates_sha256 staling on charon_rev is by-design, not a rejection reason)" \
  bash -c "awk '/^run_gate_real\(\) \{/,/^\}/' '$SCRIPT' | grep -qF -- 'bash framed_channel/check.sh --skip-approvals'"

# ============================================================================ case 16
# gate_stage_of names the command that FAILED, not an earlier one that succeeded. The test hooks
# bypass run_gate_real, so the function is lifted out of the script and fed captured-output
# fixtures directly. Under `set -e` the failing command prints last, and refresh-extraction.sh's
# own success line carries the same prefix as its failure lines -- so the last matching line is
# the right one, and the first would blame the extraction for every later failure.
gate_stage_of_case() {
  local input="$1" want="$2" got
  got="$(printf '%s\n' "$input" | bash -c "$(awk '/^gate_stage_of\(\) \{/,/^\}/' "$SCRIPT"); gate_stage_of")"
  [ "$got" = "$want" ]
}
assert_extra "gate_stage_of: externals mismatch" "a refresh-extraction.sh failure is named by its own line" \
  gate_stage_of_case $'[ok] toolchains agree\nrefresh-extraction.sh: the externals Aeneas needs differ from those FunsExternal.lean defines\n  needed: a' \
  "refresh-extraction.sh: the externals Aeneas needs differ from those FunsExternal.lean defines"
assert_extra "gate_stage_of: later check.sh failure" "an earlier refresh-extraction.sh success line is not blamed" \
  gate_stage_of_case $'refresh-extraction.sh: rewrote Types.lean and Funs.lean in aeneas/X/ (re-read the diff before committing)\nrefresh-candidates.sh: wrote certificate/candidates.txt (5 items, 5 in-subset)\n== lake build ==\n[FAIL] lake build in aeneas/ (12s)\n  see the log' \
  "[FAIL] lake build in aeneas/ (12s)"
assert_extra "gate_stage_of: coherence failure" "an aeneas_rev_coherence [FAIL] line is named" \
  gate_stage_of_case $'[ok] toolchains agree\n[FAIL] flake.lock locks aeneas aaa but aeneas/lake-manifest.json pins bbb' \
  "[FAIL] flake.lock locks aeneas aaa but aeneas/lake-manifest.json pins bbb"
assert_extra "gate_stage_of: no diagnostic line" "reports unknown" \
  gate_stage_of_case $'error: builder failed\nsome nix noise' "unknown"

if [ $failures -ne 0 ]; then
  echo "tests/bump-pin: $failures failure(s) across $case_num run_case call(s)"
  exit 1
fi
echo "tests/bump-pin: all $case_num run_case call(s) pass"
