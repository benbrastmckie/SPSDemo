#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/ladder/run.sh -- fixture tests for the proof-method ladder (lean/FramedChannel/Ladder.lean).
#
# Each fixture Lean file is copied to a temporary directory and elaborated with `lake env lean`
# from lean/, after `lake build` of the modules it imports; nothing is placed in lean/. The cases:
# an honest label passes and prints its record; a label above the cheapest closing rung, or
# outside its script's syntax class, fails; a sorry-carrying closer is not counted and nothing
# leaks; `refuted%` records the search theorem's witness and refuses a mismatched refutation.
#
# Usage: bash tests/ladder/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, the Lean toolchain pinned in lean/lean-toolchain.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
LEAN_DIR="$EX/lean"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# case|fixture|expected exit|output fragment that must appear|fragment that must NOT appear ("-": none)
CASES=(
  "honest simp label|honest-simp.lean|0|ladder FramedChannel.RingBuffer.push_fail simp|-"
  "manual label on a simp-closable goal|dishonest-manual.lean|1|is labelled manual, but the cheaper rung simp closes it|ladder FramedChannel"
  "manual label on a retrieval-closable goal|dishonest-retrieval.lean|1|is labelled manual, but the cheaper rung retrieval closes it|ladder FramedChannel"
  "label outside its syntax class|wrong-class.lean|1|is not in the syntax class of the 'simp' rung|ladder FramedChannel"
  "no rung closes; nothing leaks|sorry-retrieval.lean|0|ladder FramedChannel.RingBuffer.idx_ne manual|sorry"
  "a sorry-carrying closer is not counted|sorry-closer.lean|0|ladder FramedChannel.sorry_goal manual|cheaper rung"
  "honest refutation record|refuted-honest.lean|0|countermodel FramedChannel.small_candidate 5|-"
  "refutation of a different candidate|refuted-mismatch.lean|1|must state exactly ¬ FramedChannel.small_candidate|countermodel"
)

if ! ( cd "$LEAN_DIR" && lake build FramedChannel.Ladder FramedChannel.Model.RingBuffer.Defs ) > "$work/build.log" 2>&1; then
  echo "run.sh: could not build the ladder and the modules the fixtures import"
  tail -20 "$work/build.log"
  exit 1
fi

failures=0
for entry in "${CASES[@]}"; do
  IFS='|' read -r name fixture want_rc want_text forbid_text <<< "$entry"
  cp "$HERE/$fixture" "$work/$fixture"
  out="$(cd "$LEAN_DIR" && lake env lean "$work/$fixture" 2>&1)"
  rc=$?
  ok=true
  [ "$rc" -eq "$want_rc" ] || ok=false
  grep -qF -- "$want_text" <<< "$out" || ok=false
  if [ "$forbid_text" != "-" ] && grep -qF -- "$forbid_text" <<< "$out"; then
    ok=false
  fi
  if $ok; then
    echo "[ok] $name (exit $rc)"
  else
    echo "[FAIL] $name: exit $rc (expected $want_rc), fragment '$want_text' $(grep -qF -- "$want_text" <<< "$out" && echo found || echo missing)${forbid_text:+, forbidden '$forbid_text'}"
    sed 's/^/    /' <<< "$out"
    failures=$((failures + 1))
  fi
done

if [ $failures -ne 0 ]; then
  echo "tests/ladder/run.sh: $failures case(s) did not behave as recorded"
  exit 1
fi
echo "tests/ladder/run.sh: all ${#CASES[@]} cases behaved as recorded"
