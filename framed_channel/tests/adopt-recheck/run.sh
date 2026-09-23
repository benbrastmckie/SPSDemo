#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/adopt-recheck/run.sh -- fixture tests for scripts/adopt-recheck.sh's `--from FILE`
# validation: a valid CI-produced record (accepted, --dry-run and a real write), an identity
# mismatch, a `record:` line that is not `complete`, a `produced on:` line that does not name a
# CI producer (only `--from` enforces this), and a `verdict: ... FAIL` line. Every refusal must
# exit non-zero, name its reason, and leave certificate/recheck.txt untouched.
#
# Builds a throwaway framed_channel/ tree with its own copies of adopt-recheck.sh and
# certificate-identity.sh (adopt-recheck.sh sources the latter by path derived from its own
# location, and computes EX the same way), plus one dummy file per certificate-identity.sh's
# identity_file_list entry so identity_digest_lines succeeds.
#
# Usage: bash tests/adopt-recheck/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, coreutils (sha256sum), find. No gh, no network (every case uses --from).
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
REAL_CI="$EX/scripts/certificate-identity.sh"
REAL_ADOPT="$EX/scripts/adopt-recheck.sh"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

failures=0

FIXED_FILES=(
  aeneas/GenVectors.lean lean/FramedChannelChallenge.lean aeneas/FramedChannelAeneasChallenge.lean
  lean/lakefile.toml lean/lean-toolchain lean/lake-manifest.json
  aeneas/lakefile.toml aeneas/lean-toolchain aeneas/lake-manifest.json
  certificate/vectors.txt certificate/policy.txt certificate/candidates.txt
  check.sh scripts/refresh-hashes.sh scripts/refresh-vectors.sh scripts/refresh-extraction.sh
  scripts/lib/aeneas-revs.sh scripts/spec-check.sh scripts/refresh-candidates.sh
  scripts/lib/approval-digests.sh scripts/check-approvals.sh approve.sh
  scripts/comparator-configs.sh scripts/certificate-identity.sh scripts/check-spdx.sh
  scripts/lib/packages.sh
  recheck/lakefile.toml recheck/lean-toolchain recheck/lake-manifest.json
  scripts/lib/recheck-revs.sh
  recheck/landrun-shim.sh scripts/recheck-comparator.sh scripts/recheck-kernel.sh
  scripts/recheck-record.sh
)

# mk_tree DIR -- a throwaway framed_channel/ tree: identity_file_list's fixed members present
# (dummy content), plus copies of certificate-identity.sh and adopt-recheck.sh so both resolve
# their own EX/_certificate_identity_ex inside DIR, and a copy of the real
# scripts/lib/approval-digests.sh over the dummy one (certificate-identity.sh sources it at module
# load; the copied script must source the real lib, not the one-line dummy).
mk_tree() {
  local dir="$1" f
  mkdir -p "$dir"
  mkdir -p "$dir/rust" "$dir/lean/FramedChannel" "$dir/lean/FramedChannelChallenge" \
           "$dir/aeneas/FramedChannelAeneas" "$dir/aeneas/FramedChannelAeneasChallenge"
  for f in "${FIXED_FILES[@]}"; do
    mkdir -p "$dir/$(dirname "$f")"
    echo "fixture $f" > "$dir/$f"
  done
  cp "$REAL_CI" "$dir/scripts/certificate-identity.sh"
  cp "$REAL_ADOPT" "$dir/scripts/adopt-recheck.sh"
  cp "$EX/scripts/lib/approval-digests.sh" "$dir/scripts/lib/approval-digests.sh"
  mkdir -p "$dir/certificate"
}

# shellcheck source=/dev/null
. "$REAL_CI"

tree="$work/base"
mk_tree "$tree"
hex="$(identity_digest_lines "$tree" | identity_of_lines)"

write_candidate() {
  # write_candidate FILE FIELDS...  -- one FIELDS entry per output line, verbatim.
  local file="$1"; shift
  printf '%s\n' "$@" > "$file"
}

run_adopt() {
  # run_adopt DIR ARGS...
  local dir="$1"; shift
  ( cd "$dir" && bash scripts/adopt-recheck.sh "$@" )
}

expect() {
  # expect NAME WANT_RC WANT_TEXT -- ARGS...
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

expect_untouched() {
  # expect_untouched NAME DIR -- must be run right after a refusal case in DIR.
  local name="$1" dir="$2"
  if [ -e "$dir/certificate/recheck.txt" ]; then
    echo "[FAIL] $name: certificate/recheck.txt exists after a refusal (should be untouched)"
    failures=$((failures + 1))
  else
    echo "[ok] $name: certificate/recheck.txt left untouched"
  fi
}

# ------------------------------------------------------------------------- valid record
valid="$work/valid"; mk_tree "$valid"
cand="$work/valid.candidate.txt"
write_candidate "$cand" \
  "# fixture recheck" \
  "certificate identity: sha256:$hex" \
  "produced on: Linux x86_64 (CI: verify.yml recheck job)" \
  "record: complete"
expect "valid record: --dry-run accepted" 0 "valid, complete record" -- run_adopt "$valid" --from "$cand" --dry-run
expect_untouched "valid record: --dry-run wrote nothing" "$valid"

expect "valid record: real adoption succeeds" 0 "adopted" -- run_adopt "$valid" --from "$cand"
if [ -f "$valid/certificate/recheck.txt" ] && cmp -s "$cand" "$valid/certificate/recheck.txt"; then
  echo "[ok] valid record: certificate/recheck.txt written byte-for-byte"
else
  echo "[FAIL] valid record: certificate/recheck.txt missing or not byte-identical to the candidate"
  failures=$((failures + 1))
fi

# ------------------------------------------------------------------------- identity mismatch
mismatch="$work/mismatch"; mk_tree "$mismatch"
cand="$work/mismatch.candidate.txt"
write_candidate "$cand" \
  "# fixture recheck" \
  "certificate identity: sha256:0000000000000000000000000000000000000000000000000000000000000000" \
  "produced on: Linux x86_64 (CI: verify.yml recheck job)" \
  "record: complete"
expect "identity mismatch: refused" 1 "is for identity" -- run_adopt "$mismatch" --from "$cand" --dry-run
expect_untouched "identity mismatch" "$mismatch"

# ------------------------------------------------------------------------- record: not complete
partial="$work/partial"; mk_tree "$partial"
cand="$work/partial.candidate.txt"
write_candidate "$cand" \
  "# fixture recheck" \
  "certificate identity: sha256:$hex" \
  "produced on: Linux x86_64 (CI: verify.yml recheck job)" \
  "record: partial (Comparator NOT-RUN)"
expect "record not complete: refused" 1 "is not a complete record" -- run_adopt "$partial" --from "$cand" --dry-run
expect_untouched "record not complete" "$partial"

# ------------------------------------------------------------------------- local produced on:
local_rec="$work/localrec"; mk_tree "$local_rec"
cand="$work/localrec.candidate.txt"
write_candidate "$cand" \
  "# fixture recheck" \
  "certificate identity: sha256:$hex" \
  "produced on: Linux x86_64 (local)" \
  "record: complete"
expect "local produced-on line: refused" 1 "does not name a CI recheck producer" -- run_adopt "$local_rec" --from "$cand" --dry-run
expect_untouched "local produced-on line" "$local_rec"

# ------------------------------------------------------------------------- verdict FAIL
failverdict="$work/failverdict"; mk_tree "$failverdict"
cand="$work/failverdict.candidate.txt"
write_candidate "$cand" \
  "# fixture recheck" \
  "certificate identity: sha256:$hex" \
  "produced on: Linux x86_64 (CI: verify.yml recheck-arm job)" \
  "record: complete" \
  "verdict: kernel comparator FAIL"
expect "verdict FAIL: refused" 1 "records a FAIL verdict" -- run_adopt "$failverdict" --from "$cand" --dry-run
expect_untouched "verdict FAIL" "$failverdict"

# ------------------------------------------------------------------------- usage errors
expect "unknown argument" 2 "unknown argument" -- run_adopt "$valid" --bogus
expect "no such file" 1 "does not exist" -- run_adopt "$valid" --from "$work/does-not-exist.txt"

if [ "$failures" -eq 0 ]; then
  echo "adopt-recheck: PASS"
  exit 0
fi
echo "adopt-recheck: FAIL ($failures case(s))"
exit 1
