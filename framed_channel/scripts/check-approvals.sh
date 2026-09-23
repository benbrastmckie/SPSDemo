#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# check-approvals.sh -- verify that the approvals in an approvals file are current. READ-ONLY.
#
# The selection must match today's source_sha256 and candidates_sha256 (approval-digests.sh) and
# decide exactly the in-subset candidates, selecting exactly the reached ones when the bridge
# package is checked; each Challenge module needs one record at today's spec_digest. Every record
# says whether a person or an agent approved it. An absent file fails. Rules and limits: certificate/README.md.
#
# Usage: bash scripts/check-approvals.sh FILE (--core-only | --aeneas | --spec-records FILE)
#                                [--candidates FILE] [--require-person] [-h | --help]
#   FILE                  the approvals file (check.sh passes certificate/approvals.yaml)
#   --core-only/--aeneas  which packages' Challenge modules are checked (as spec-check.sh);
#                         required unless --spec-records is given
#   --spec-records FILE   spec-check.sh output to use instead of running spec-check.sh (its own
#                         records already determine the scope checked)
#   --candidates FILE     the candidate file (default certificate/candidates.txt)
#   --require-person      fail any record approved by an agent (by: agent)
#
# Requires: bash >= 4.4, coreutils, awk; git for the stale-digest hint; without --spec-records,
# what spec-check.sh requires.
# Exit: 0 every checked record current, 1 a record is absent or stale, 2 usage error or missing
# prerequisite.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/approval-digests.sh
. "$EX/scripts/lib/approval-digests.sh"
# shellcheck source=lib/packages.sh
. "$EX/scripts/lib/packages.sh"

file=""
spec_records=""
require_person=false
candidates="$EX/certificate/candidates.txt"
while [ "$#" -gt 0 ]; do
  case "$1" in
    --core-only|--aeneas) bridge_scope_arg check-approvals.sh "$1" || exit $?; shift ;;
    --spec-records)
      [ "$#" -ge 2 ] || { echo "check-approvals.sh: --spec-records needs a file" >&2; exit 2; }
      spec_records="$2"; shift 2 ;;
    --candidates)
      [ "$#" -ge 2 ] || { echo "check-approvals.sh: --candidates needs a file" >&2; exit 2; }
      candidates="$2"; shift 2 ;;
    --require-person) require_person=true; shift ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    -*) echo "check-approvals.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
    *)
      [ -z "$file" ] || { echo "check-approvals.sh: more than one FILE given" >&2; exit 2; }
      file="$1"; shift ;;
  esac
done
[ -n "$file" ] || { echo "check-approvals.sh: no approvals FILE given (try --help)" >&2; exit 2; }
if [ -z "$spec_records" ] && [ -z "${bridge_scope:-}" ]; then
  echo "check-approvals.sh: give --core-only or --aeneas (or --spec-records FILE, whose own records already determine the scope checked)" >&2
  exit 2
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

failures=0
fail() {
  echo "[FAIL] $*"
  failures=$((failures + 1))
}

# ------------------------------------------------------------------------------ inputs

if [ ! -f "$file" ]; then
  echo "[FAIL] approvals: $file does not exist. No selection or specification has been approved."
  echo "  Write a review file, review it, then record it (see certificate/README.md):"
  echo "    bash approve.sh --review --all --out review.md --aeneas"
  echo "    bash approve.sh --record review.md --approver \"Name <email>\" --aeneas     (a person, at a terminal)"
  echo "    bash approve.sh --record review.md --approver \"Name (agent) <email>\" --agent --aeneas"
  exit 1
fi
if [ ! -f "$candidates" ]; then
  echo "check-approvals.sh: candidate file $candidates is missing" >&2
  exit 2
fi

if [ -z "$spec_records" ]; then
  args=()
  case "$bridge_scope" in
    core) args+=(--core-only) ;;
    aeneas) args+=(--aeneas) ;;
  esac
  if ! bash "$EX/scripts/spec-check.sh" "${args[@]}" > "$work/spec" 2> "$work/spec.err"; then
    cat "$work/spec.err" >&2
    echo "check-approvals.sh: spec-check.sh failed" >&2
    exit 1
  fi
  spec_records="$work/spec"
fi
[ -f "$spec_records" ] || { echo "check-approvals.sh: no spec records at $spec_records" >&2; exit 2; }

# Which packages the records cover: exactly those with a record.
bridge_checked=false
grep -q '^bridge ' "$spec_records" && bridge_checked=true

if ! approvals_normalize "$file" > "$work/records"; then
  grep '^parse-error' "$work/records" | cut -f2- | sed "s|^|[FAIL] approvals: $file line |"
  echo "check-approvals.sh: the approvals file does not have the recorded shape (see approval-digests.sh)"
  exit 1
fi

# date_valid YYYY-MM-DD: a real calendar date (month lengths and leap years), without GNU date.
date_valid() {
  [[ "$1" =~ ^([0-9]{4})-([0-9]{2})-([0-9]{2})$ ]] || return 1
  local y=$((10#${BASH_REMATCH[1]})) m=$((10#${BASH_REMATCH[2]})) d=$((10#${BASH_REMATCH[3]})) days
  case "$m" in
    1|3|5|7|8|10|12) days=31 ;;
    4|6|9|11) days=30 ;;
    2) days=28; (( (y % 4 == 0 && y % 100 != 0) || y % 400 == 0 )) && days=29 ;;
    *) return 1 ;;
  esac
  (( d >= 1 && d <= days ))
}

# stale_hint DIGEST PATHS...: the commit that recorded DIGEST, and what changed in PATHS since.
stale_hint() {
  local digest="$1" commit
  shift
  git -C "$EX" rev-parse --git-dir > /dev/null 2>&1 || return 0
  commit="$(approval_commit "$digest" "$EX")"
  if [ -z "$commit" ]; then
    echo "  (no commit records the approved digest $digest; the approval is not committed)"
    return
  fi
  echo "  approved in commit $commit (git log -S$digest -- certificate/approvals.yaml); changes since:"
  echo "    git diff $commit -- $*"
  git -C "$EX" diff --stat "$commit" -- "$@" 2>/dev/null | sed 's/^/    /' | tail -20
}

# check_by WHAT APPROVER BY: BY is person or agent, consistent with APPROVER, and allowed.
check_by() {
  case "$3" in
    person|agent) ;;
    *) fail "approvals: $1 has by '$3', not 'person' or 'agent'"; return ;;
  esac
  approver_matches_by "$2" "$3" ||
    fail "approvals: $1 has by '$3' but approver '$2' (an agent approver is named 'Name (agent) <email>'; a person's is not)"
  if $require_person && [ "$3" = agent ]; then
    fail "approvals: $1 was approved by an agent ($2), and --require-person is set"
  fi
}

# ---------------------------------------------------------------------------- selection

awk -F'\t' '$1 == "sel" && ($2 == "candidates_sha256" || $2 == "source_sha256" || $2 == "approver" || $2 == "by" || $2 == "date") { print $2 "\t" $3 }' "$work/records" > "$work/sel.fields"
sel_field() {
  awk -F'\t' -v k="$1" '$1 == k { print $2 }' "$work/sel.fields"
}
if ! grep -q '^sel	' "$work/records"; then
  fail "approvals: no selection record (the selection has not been approved)"
else
  for k in candidates_sha256 source_sha256 approver by date; do
    n="$(awk -F'\t' -v k="$k" '$1 == k' "$work/sel.fields" | grep -c .)"
    if [ "$n" -eq 0 ]; then fail "approvals: the selection record has no $k"; fi
    if [ "$n" -gt 1 ]; then fail "approvals: the selection record has $n $k fields"; fi
  done
  approver="$(sel_field approver | head -1)"
  date_v="$(sel_field date | head -1)"
  by_v="$(sel_field by | head -1)"
  check_by "the selection" "$approver" "$by_v"
  approver_valid "$approver" || fail "approvals: selection approver '$approver' is not of the form 'Name <email>'"
  date_valid "$date_v" || fail "approvals: selection date '$date_v' is not a YYYY-MM-DD date"

  cur_src="$(source_sha256 "$EX")" || { echo "check-approvals.sh: cannot digest rust/" >&2; exit 2; }
  cur_cand="$(sha256sum "$candidates" | cut -d' ' -f1)"
  rec_src="$(sel_field source_sha256 | head -1)"
  rec_cand="$(sel_field candidates_sha256 | head -1)"
  if [ "$rec_src" != "$cur_src" ]; then
    fail "approvals: the selection is stale: the Rust changed since it was approved (source_sha256 recorded $rec_src, now $cur_src)"
    stale_hint "$rec_src" rust/src rust/Cargo.toml rust/Cargo.lock
  fi
  if [ "$rec_cand" != "$cur_cand" ]; then
    fail "approvals: the selection is stale: the candidate set changed since it was approved (candidates_sha256 recorded $rec_cand, now $cur_cand)"
    stale_hint "$rec_cand" certificate/candidates.txt
  fi

  awk -F'\t' '$1 == "sel" && $2 == "selected" { print $3 }' "$work/records" | LC_ALL=C sort > "$work/selected.all"
  awk -F'\t' '$1 == "sel" && $2 == "declined" { print $3 }' "$work/records" | LC_ALL=C sort > "$work/declined.all"
  for list in selected declined; do
    fail_each failures "approvals: %s is listed more than once under $list" <<< "$(uniq -d "$work/$list.all")"
    uniq "$work/$list.all" > "$work/$list"
  done
  awk -F'\t' '$1 == "sel" && $2 == "declined" && $4 ~ /^[[:space:]]*$/ { print $3 }' "$work/records" |
    while IFS= read -r n; do echo "[FAIL] approvals: declined $n has an empty reason"; done > "$work/emptyreason"
  if [ -s "$work/emptyreason" ]; then
    cat "$work/emptyreason"
    failures=$((failures + $(grep -c . "$work/emptyreason")))
  fi
  fail_each failures "approvals: %s is both selected and declined" \
    <<< "$(LC_ALL=C comm -12 "$work/selected" "$work/declined")"

  insubset_candidates "$candidates" > "$work/insubset"
  LC_ALL=C sort -u "$work/selected" "$work/declined" > "$work/decided"
  fail_each failures "approvals: in-subset candidate %s is neither selected nor declined" \
    <<< "$(LC_ALL=C comm -23 "$work/insubset" "$work/decided")"
  fail_each failures "approvals: %s is selected or declined but is not an in-subset candidate" \
    <<< "$(LC_ALL=C comm -13 "$work/insubset" "$work/decided")"

  if $bridge_checked; then
    awk '$1 == "bridge" && $2 == "reached" { print $3 }' "$spec_records" | LC_ALL=C sort -u > "$work/reached"
    LC_ALL=C comm -12 "$work/insubset" "$work/reached" > "$work/reached.insubset"
    fail_each failures "approvals: %s is selected, but no registered statement is about it (no statement closure reaches it)" \
      <<< "$(LC_ALL=C comm -23 "$work/selected" "$work/reached.insubset")"
    fail_each failures "approvals: %s is specified (a registered statement's closure reaches it) but not selected" \
      <<< "$(LC_ALL=C comm -13 "$work/selected" "$work/reached.insubset")"
    sel_reach="selected == the reached in-subset candidates"
  else
    sel_reach="selected-versus-reached NOT CHECKED (bridge package not checked)"
  fi
  if [ $failures -eq 0 ]; then
    echo "[ok] approvals: selection current ($(grep -c . "$work/selected") selected, $(grep -c . "$work/declined") declined, by $approver ($by_v) on $date_v; $sel_reach)"
  fi
fi

# ------------------------------------------------------------------------ specification

sel_failures=$failures
awk '$2 == "digest" { print $1 "\t" $3 "\t" $4 }' "$spec_records" | LC_ALL=C sort > "$work/digests"
awk -F'\t' '$1 == "spec" { print $2 "\t" $3 "\t" $4 }' "$work/records" > "$work/spec.recs"
nrec="$(cut -f1 "$work/spec.recs" | LC_ALL=C sort -u | grep -c .)"

# imported_defs (scripts/lib/approval-digests.sh) is used below.

declare -A recorded=()
agent_records=0
spec_unchecked=0
for i in $(cut -f1 "$work/spec.recs" | LC_ALL=C sort -un); do
  get() { awk -F'\t' -v i="$i" -v k="$1" '$1 == i && $2 == k { print $3 }' "$work/spec.recs"; }
  m="$(get challenge)"; d="$(get spec_digest)"; a="$(get approver)"; dt="$(get date)"; b="$(get by)"
  for k in spec_digest approver by date; do
    [ "$(get "$k" | grep -c .)" -eq 1 ] || fail "approvals: specification record $i ($m) must have exactly one $k"
  done
  approver_valid "$a" || fail "approvals: specification record for $m has approver '$a', not of the form 'Name <email>'"
  date_valid "$dt" || fail "approvals: specification record for $m has date '$dt', not a YYYY-MM-DD date"
  check_by "the specification record for $m" "$a" "$b"
  [ "$b" = agent ] && agent_records=$((agent_records + 1))
  if [ -n "${recorded[$m]:-}" ]; then
    fail "approvals: $m is recorded more than once"
    continue
  fi
  recorded[$m]="$d"
  if ! pkg="$(challenge_package "$m")" || ! rel="$(challenge_file "$m")" || [ ! -f "$EX/$rel" ]; then
    fail "approvals: a specification record names $m, which is not a Challenge module"
    continue
  fi
  if ! grep -q "^$pkg " "$spec_records"; then
    spec_unchecked=$((spec_unchecked + 1))
    continue
  fi
  cur="$(awk -F'\t' -v p="$pkg" -v m="$m" '$1 == p && $2 == m { print $3 }' "$work/digests")"
  if [ -z "$cur" ]; then
    fail "approvals: a specification record names $m, but SpecCheck reports no digest for it (it declares no theorem)"
  elif [ "$cur" != "$d" ]; then
    fail "approvals: the specification $m is stale: it changed since it was approved (spec_digest recorded $d, now $cur)"
    # shellcheck disable=SC2046
    stale_hint "$d" "$rel" $(imported_defs "$rel")
  fi
done
while IFS=$'\t' read -r pkg m cur; do
  [ -z "$m" ] && continue
  if [ -z "${recorded[$m]:-}" ]; then
    fail "approvals: no specification record for $m (its current spec_digest is $cur): it has not been approved"
  fi
done < "$work/digests"

if [ $failures -eq $sel_failures ]; then
  msg="$(grep -c . "$work/digests") Challenge module(s) checked"
  $bridge_checked || msg="$msg; bridge records NOT CHECKED (bridge package not checked)"
  [ $spec_unchecked -eq 0 ] || msg="$msg; $spec_unchecked record(s) of an unchecked package NOT CHECKED"
  echo "[ok] approvals: specification current ($msg; $nrec record(s), $agent_records by an agent)"
fi

if [ $failures -ne 0 ]; then
  echo "check-approvals.sh: $failures approval failure(s) in $file"
  exit 1
fi
exit 0
