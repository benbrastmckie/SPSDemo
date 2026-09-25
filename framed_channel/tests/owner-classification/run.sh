#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/owner-classification/run.sh -- fixture tests for check.sh's owner_of_proof and
# owner_of_supporting.
#
# A supporting: name is spliced into a grep -E pattern to find its own '#print axioms' line, so
# every ERE metacharacter in the name must be escaped -- not just '.'. An under-escaped name
# (e.g. one ending in '?') is read as a quantifier, never matches its own line, and is
# misclassified as core-owned; under --core-only that turns a correct unaudited exemption into a
# spurious [FAIL]. These cases pin both the reported defect shape (a name ending in '?') and its
# generality (a name with a different metacharacter), plus the negative half (a name with no
# matching line at all) and a near-miss (anchoring must still bind, not just escaping).
#
# No copy of the rules lives here. The runner extracts check.sh's own `# >>> owner-rules` block
# (owner_of_proof and owner_of_supporting, verbatim) and calls the real functions against fixture
# trees, so a narrowing of the escape set drifts this suite too.
#
# Usage: bash tests/owner-classification/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, coreutils. No Lean toolchain, no build.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_EX="$(cd "$HERE/../.." && pwd)"

block="$(sed -n '/^# >>> owner-rules/,/^# <<< owner-rules/p' "$REPO_EX/check.sh")"
if [ -z "$block" ]; then
  echo "[FAIL] check.sh has no '# >>> owner-rules' ... '# <<< owner-rules' block to extract"
  echo "       (the markers are load-bearing: this self-test exercises the gate's real functions)"
  exit 1
fi
# shellcheck disable=SC2034  # work is read by the extracted block (owner_of_proof)
work="$(mktemp -d)"
: > "$work/registered.bridge"
eval "$block"

# A throwaway bridge tree for the synthetic cases: one name ending in '?' (the reported defect
# shape), one with a different metacharacter (pins generality -- a '?'-only patch fails this
# case), one plain dotted name (no regression for the common case), and one name ('Some.Name')
# used only for the near-miss case below. Deliberately absent: any line for the "no match" and
# "near-miss query" names, so their negative expectation is genuine.
SYN_EX="$(mktemp -d)"
trap 'rm -rf "$work" "$SYN_EX"' EXIT
mkdir -p "$SYN_EX/aeneas/FramedChannelAeneas/Fixture"
cat > "$SYN_EX/aeneas/FramedChannelAeneas/Fixture/Fixture.lean" <<'EOF'
#print axioms FramedChannel.Bridge.stuff.eq_getElem_of_getElem?
#print axioms FramedChannel.Bridge.plus.foo+bar
#print axioms FramedChannel.Bridge.plain.name
#print axioms Some.Name
EOF

# name|ex root variable name|queried name|expect ("bridge" or "core")
CASES=(
  "a name ending in '?' classifies bridge (the reported defect)|SYN_EX|FramedChannel.Bridge.stuff.eq_getElem_of_getElem?|bridge"
  "a name with a non-'?' metacharacter classifies bridge (pins generality)|SYN_EX|FramedChannel.Bridge.plus.foo+bar|bridge"
  "a plain dotted name with a matching line classifies bridge (no regression)|SYN_EX|FramedChannel.Bridge.plain.name|bridge"
  "a name with no #print axioms line anywhere classifies core|SYN_EX|FramedChannel.NoSuchName.AtAll|core"
  "a near-miss is not matched: the fixture name is a strict prefix of the query|SYN_EX|Some.NameX|core"
  "the real eq_getElem_of_getElem? name classifies bridge against the real bridge tree|REPO_EX|FramedChannel.Bridge.stuff.eq_getElem_of_getElem?|bridge"
  "the real getElem?_some_lt name classifies bridge against the real bridge tree|REPO_EX|FramedChannel.Bridge.stuff.getElem?_some_lt|bridge"
)

failures=0
for entry in "${CASES[@]}"; do
  IFS='|' read -r name ex_var query expect <<< "$entry"
  ex="${!ex_var}"
  # shellcheck disable=SC2034  # EX is read by the extracted block (owner_of_supporting)
  got="$(EX="$ex" owner_of_supporting "$query")"
  if [ "$got" = "$expect" ]; then
    echo "[ok] $name ($got)"
  else
    echo "[FAIL] $name: classified $got, expected $expect"
    failures=$((failures + 1))
  fi
done

# owner_of_proof is exercised too, since it shares the extracted block: a name present in
# $work/registered.bridge is bridge-owned; any other name is core-owned. No regex is built here
# (grep -qxF), so this is a smoke check, not a regression pin.
printf '%s\n' "FramedChannel.some_proof" > "$work/registered.bridge"
if [ "$(owner_of_proof "FramedChannel.some_proof")" = bridge ] \
  && [ "$(owner_of_proof "FramedChannel.other_proof")" = core ]; then
  echo "[ok] owner_of_proof classifies a registered name bridge and an unregistered name core"
else
  echo "[FAIL] owner_of_proof misclassified a registered or unregistered name"
  failures=$((failures + 1))
fi

if [ $failures -ne 0 ]; then
  echo "tests/owner-classification/run.sh: $failures case(s) did not behave as recorded"
  exit 1
fi
echo "tests/owner-classification/run.sh: ${#CASES[@]} case(s) plus owner_of_proof behaved as recorded"
