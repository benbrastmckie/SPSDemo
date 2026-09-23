#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/recheck-record/run.sh -- fixture tests for scripts/recheck-record.sh: canned
# comparator.verdicts/kernel.verdicts/comparator.deviations and a coherence text render into a
# record whose shape and exit code match the case (complete, PARTIAL from a Comparator NOT-RUN,
# a FAIL verdict, an unrecognised verdict, a missing verdict file), plus a golden check that the
# "## verdicts" section it renders from the REAL committed certificate/recheck.txt's own verdict
# data (at 04f8743) is byte-identical to that file's own "## verdicts" section -- proof the
# verdict-line transformation this script now owns is output-preserving relative to check.sh's
# pre-extraction inline version. (Scope note: only the "## verdicts" section is golden-checked
# against the committed file; "## sandbox deviations" needs 11 grant groups over 3 rooms to
# reproduce exactly and is instead covered by the smaller canned-deviations case below, which
# checks the grouping/sort transformation on a tractable input.)
#
# Usage: bash tests/recheck-record/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, awk, coreutils, git (for the golden-seed case only; skipped if git or
# the 04f8743 commit is unavailable).
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
SCRIPT="$EX/scripts/recheck-record.sh"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

failures=0

# mk_case NAME: a fresh work-dir/coherence-file/complete-out/partial-out set under $work/NAME.
mk_case() {
  local dir="$work/$1"
  mkdir -p "$dir/wd"
  echo "[ok] fixture coherence line" > "$dir/coherence.txt"
  printf '%s\n' "$dir"
}

run_record() {
  # run_record CASE_DIR -- extra recheck-record.sh args
  local dir="$1"; shift
  bash "$SCRIPT" --work-dir "$dir/wd" --coherence-file "$dir/coherence.txt" \
    --identity "sha256:$(printf '%064d' 0)" \
    --complete-out "$dir/recheck.txt" --partial-out "$dir/recheck.partial.txt" "$@" 2>&1
}

expect() {
  # expect NAME WANT_RC WANT_TEXT -- COMMAND...
  local name="$1" want_rc="$2" want_text="$3"
  shift 4
  local out rc
  out="$("$@" 2>&1)"
  rc=$?
  if [ "$rc" -eq "$want_rc" ] && { [ -z "$want_text" ] || grep -qF -- "$want_text" <<< "$out"; }; then
    echo "[ok] $name (exit $rc)"
  else
    echo "[FAIL] $name: exit $rc (expected $want_rc), text '$want_text'"
    sed 's/^/    /' <<< "$out"
    failures=$((failures + 1))
  fi
}

# ---------------------------------------------------------------------------- complete
c="$(mk_case complete)"
printf 'core OK 1 Your solution is okay!\n' > "$c/wd/comparator.verdicts"
printf 'lean4lean core OK modules=1 declarations=2 1 replayed\n' > "$c/wd/kernel.verdicts"
: > "$c/wd/comparator.deviations"
expect "complete: exit 0" 0 "written to" -- run_record "$c"
if grep -qx 'record: complete' "$c/recheck.txt" 2>/dev/null; then
  echo "[ok] complete: recheck.txt has record: complete"
else
  echo "[FAIL] complete: recheck.txt missing or not record: complete"
  failures=$((failures + 1))
fi
if [ -e "$c/recheck.partial.txt" ]; then
  echo "[FAIL] complete: recheck.partial.txt should not exist"
  failures=$((failures + 1))
else
  echo "[ok] complete: recheck.partial.txt not written"
fi

# ---------------------------------------------------------------------- partial (Comparator NOT-RUN)
c="$(mk_case partial)"
printf 'core NOT-RUN 0 Landlock sandbox is Linux-only\n' > "$c/wd/comparator.verdicts"
printf 'lean4lean core OK modules=1 declarations=2 1 replayed\n' > "$c/wd/kernel.verdicts"
: > "$c/wd/comparator.deviations"
expect "partial: exit 2" 2 "PARTIAL" -- run_record "$c"
if grep -q '^record: PARTIAL' "$c/recheck.partial.txt" 2>/dev/null; then
  echo "[ok] partial: recheck.partial.txt has a PARTIAL record: line"
else
  echo "[FAIL] partial: recheck.partial.txt missing or not PARTIAL"
  failures=$((failures + 1))
fi
if [ -e "$c/recheck.txt" ]; then
  echo "[FAIL] partial: recheck.txt should not exist"
  failures=$((failures + 1))
else
  echo "[ok] partial: recheck.txt not written"
fi

# ---------------------------------------------------------------------------- FAIL verdict
c="$(mk_case failverdict)"
printf 'core FAIL 1 something went wrong\n' > "$c/wd/comparator.verdicts"
printf 'lean4lean core OK modules=1 declarations=2 1 replayed\n' > "$c/wd/kernel.verdicts"
: > "$c/wd/comparator.deviations"
expect "FAIL verdict: exit 1" 1 "FAILED" -- run_record "$c"
if grep -q '^verdict: comparator core FAIL' "$c/recheck.txt" "$c/recheck.partial.txt" 2>/dev/null; then
  echo "[ok] FAIL verdict: a record was written naming the FAIL"
else
  echo "[FAIL] FAIL verdict: no record found with the FAIL verdict line"
  failures=$((failures + 1))
fi

# ---------------------------------------------------------------------------- unrecognised verdict
c="$(mk_case badverdict)"
printf 'core WEIRD 1 not a real verdict\n' > "$c/wd/comparator.verdicts"
printf 'lean4lean core OK modules=1 declarations=2 1 replayed\n' > "$c/wd/kernel.verdicts"
: > "$c/wd/comparator.deviations"
expect "unrecognised verdict: exit 1" 1 "unrecognised verdict" -- run_record "$c"

# ---------------------------------------------------------------------------- missing verdict file
c="$(mk_case missing)"
printf 'lean4lean core OK modules=1 declarations=2 1 replayed\n' > "$c/wd/kernel.verdicts"
expect "missing comparator.verdicts: exit 3" 3 "is missing" -- run_record "$c"

# ---------------------------------------------------------------------------- usage
expect "unknown argument" 3 "unknown argument" -- bash "$SCRIPT" --bogus

# ------------------------------------------------------ deviations grouping (canned, tractable)
c="$(mk_case deviations)"
printf 'core OK 1 Your solution is okay!\nbridge OK 1 Your solution is okay!\n' > "$c/wd/comparator.verdicts"
printf 'lean4lean core OK modules=1 declarations=2 1 replayed\n' > "$c/wd/kernel.verdicts"
printf 'core --env CI=true\nbridge --env CI=true\ncore --rwx /some/path\n' > "$c/wd/comparator.deviations"
run_record "$c" > /dev/null
if grep -qxF -- '--env CI=true  [core,bridge]' "$c/recheck.txt" && grep -qxF -- '--rwx /some/path  [core]' "$c/recheck.txt"; then
  echo "[ok] deviations: grants grouped and sorted correctly"
else
  echo "[FAIL] deviations: expected grouped/sorted deviation lines not found"
  sed -n '/## sandbox deviations/,/## hardening/p' "$c/recheck.txt" | sed 's/^/    /'
  failures=$((failures + 1))
fi

# -------------------------------------------------- golden: verdicts section from the real file
if command -v git > /dev/null 2>&1 && git -C "$EX" cat-file -e 04f8743:framed_channel/certificate/recheck.txt 2> /dev/null; then
  c="$(mk_case golden)"
  git -C "$EX" show 04f8743:framed_channel/certificate/recheck.txt > "$c/committed-recheck.txt"
  # Reconstruct the raw comparator.verdicts / kernel.verdicts inputs from the committed record's
  # own "## verdicts" section (reversing recheck-record.sh's transformation: comparator rows drop
  # the leading "comparator" label and insert a placeholder seconds field before the note; kernel
  # rows likewise insert a placeholder seconds field between declarations=D and the note).
  : > "$c/wd/comparator.verdicts"
  : > "$c/wd/kernel.verdicts"
  awk -v cfile="$c/wd/comparator.verdicts" -v kfile="$c/wd/kernel.verdicts" '
    /^verdict: comparator / {
      line = $0; sub(/^verdict: comparator /, "", line)
      n = split(line, f, " ")
      rest = ""; for (i = 3; i <= n; i++) rest = rest (rest == "" ? "" : " ") f[i]
      print f[1], f[2], 0, rest >> cfile
      next
    }
    /^verdict: / {
      line = $0; sub(/^verdict: /, "", line)
      n = split(line, f, " ")
      rest = ""; for (i = 6; i <= n; i++) rest = rest (rest == "" ? "" : " ") f[i]
      print f[1], f[2], f[3], f[4], f[5], 0, rest >> kfile
      next
    }
  ' "$c/committed-recheck.txt"
  : > "$c/wd/comparator.deviations"
  bash "$SCRIPT" --work-dir "$c/wd" --coherence-file "$c/coherence.txt" \
    --identity "sha256:$(printf '%064d' 0)" \
    --complete-out "$c/recheck.txt" --partial-out "$c/recheck.partial.txt" > /dev/null 2>&1
  got="$(sed -n '/^## verdicts/,/^$/p' "$c/recheck.txt" 2>/dev/null)"
  want="$(sed -n '/^## verdicts/,/^$/p' "$c/committed-recheck.txt")"
  if [ "$got" = "$want" ]; then
    echo "[ok] golden: the rendered ## verdicts section matches the committed recheck.txt (04f8743) exactly"
  else
    echo "[FAIL] golden: rendered ## verdicts section differs from the committed recheck.txt"
    diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | sed 's/^/    /'
    failures=$((failures + 1))
  fi
else
  echo "[skip] golden: git or commit 04f8743 unavailable in this checkout"
fi

if [ "$failures" -eq 0 ]; then
  echo "recheck-record: PASS"
  exit 0
fi
echo "recheck-record: FAIL ($failures case(s))"
exit 1
