#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# adopt-recheck.sh -- adopt a CI-produced independent recheck record as certificate/recheck.txt.
#
# `check.sh --recheck` on a non-Linux host (or a Linux host without systemd/landrun) can only
# ever write a PARTIAL record (certificate/recheck.partial.txt; see check.sh and
# scripts/lib/recheck-revs.sh's recheck_record_completeness). The canonical, complete record is
# produced by CI (.github/workflows/verify.yml's `recheck` job, ubuntu-24.04, which sets
# RECHECK_PRODUCER and uploads its record as the `recheck-record` artifact). This script is the
# local, one-command path from that artifact to a committed, complete certificate/recheck.txt --
# consistent with this repository's posture that CI never commits or pushes: the contributor
# does, after this script validates the record.
#
# NOT a certificate-identity input: this script does not influence any verdict, and is
# deliberately absent from scripts/certificate-identity.sh's identity_file_list. Editing it never
# changes the tree's identity or requires a certificate regeneration.
#
# Usage: bash scripts/adopt-recheck.sh [--run ID | --from FILE] [--dry-run] [-h | --help]
#   --run ID     adopt the `recheck-record` artifact of verify.yml run ID (via `gh run download`)
#   --from FILE  adopt FILE directly, without `gh` (e.g. an already-downloaded artifact member)
#   --dry-run    validate and report, but do not write certificate/recheck.txt
#   (no option)  find the latest verify.yml run for the current branch whose head commit is HEAD,
#                and adopt its `recheck-record` artifact
#
# Validation, before anything is copied: the candidate's `certificate identity:` line equals this
# tree's identity (scripts/certificate-identity.sh); it carries `record: complete` (never a
# PARTIAL record); it carries a `produced on:` line naming a genuine CI producer (`--from FILE`
# only -- see below); and no `verdict:` line is FAIL. Any failure refuses with a specific reason
# -- nothing is written, and certificate/recheck.txt is untouched.
#
# `--from FILE`'s producer check: `--run`/the no-option path always download from a genuine CI
# artifact, so only `--from FILE` can smuggle in a locally-produced record. This script enforces
# that a `--from FILE` candidate's `produced on:` line names one of verify.yml's two
# RECHECK_PRODUCER_NAME values ("verify.yml recheck job" or "verify.yml recheck-arm job");
# anything else (e.g. a local `Linux x86_64 (local)` record) is refused.
#
# On success, the candidate is copied byte-for-byte to certificate/recheck.txt. This script never
# runs `git add` or `git commit` (and never pushes): review the diff and commit it yourself.
#
# Requires: bash >= 4.4, coreutils. `--run` and the no-option auto-discovery form also need `gh`
# (authenticated) and `git`.
# Exit: 0 adopted (or, with --dry-run, validated), 1 the record was refused or a lookup failed,
# 2 usage error.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CERT="$EX/certificate"
RECHECK="$CERT/recheck.txt"

# The two RECHECK_PRODUCER_NAME values .github/workflows/verify.yml's recheck and recheck-arm
# jobs set (see verify.yml's own RECHECK_PRODUCER_NAME lines). A --from FILE record whose
# `produced on:` line names neither is refused below: --run and the no-option auto-discovery
# path always download from a genuine CI artifact, so only --from FILE can smuggle a
# locally-produced record in as if it were CI-produced.
CI_PRODUCER_1="verify.yml recheck job"
CI_PRODUCER_2="verify.yml recheck-arm job"

# shellcheck source=certificate-identity.sh
. "$EX/scripts/certificate-identity.sh"

run_id=""
from_file=""
dry_run=false
while [ "$#" -gt 0 ]; do
  case "$1" in
    --run)
      [ "$#" -ge 2 ] || { echo "adopt-recheck.sh: --run needs a run ID" >&2; exit 2; }
      run_id="$2"; shift 2 ;;
    --from)
      [ "$#" -ge 2 ] || { echo "adopt-recheck.sh: --from needs a file path" >&2; exit 2; }
      from_file="$2"; shift 2 ;;
    --dry-run) dry_run=true; shift ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "adopt-recheck.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done
if [ -n "$run_id" ] && [ -n "$from_file" ]; then
  echo "adopt-recheck.sh: --run and --from are mutually exclusive" >&2
  exit 2
fi

work=""
cleanup() { [ -n "$work" ] && rm -rf "$work"; }
trap cleanup EXIT

candidate=""
run_url=""

if [ -n "$from_file" ]; then
  [ -f "$from_file" ] || { echo "adopt-recheck.sh: $from_file does not exist" >&2; exit 1; }
  candidate="$from_file"
else
  command -v gh > /dev/null 2>&1 || {
    echo "adopt-recheck.sh: gh (GitHub CLI) is not on PATH; install it, or use --from FILE with an" >&2
    echo "  already-downloaded recheck-record artifact member (e.g. after 'gh run download' by hand)." >&2
    exit 1
  }
  command -v git > /dev/null 2>&1 || { echo "adopt-recheck.sh: git is not on PATH" >&2; exit 1; }
  gh auth status > /dev/null 2>&1 || {
    echo "adopt-recheck.sh: gh is not authenticated; run 'gh auth login' first" >&2
    exit 1
  }

  if [ -z "$run_id" ]; then
    branch="$(git -C "$EX" rev-parse --abbrev-ref HEAD 2>/dev/null)" || {
      echo "adopt-recheck.sh: could not determine the current branch (detached HEAD?); pass --run ID explicitly" >&2
      exit 1
    }
    head_sha="$(git -C "$EX" rev-parse HEAD)"
    runs_json="$(gh run list --workflow=verify.yml --branch "$branch" --limit 20 \
      --json databaseId,headSha,url,status,conclusion 2>&1)" || {
      echo "adopt-recheck.sh: gh run list failed:" >&2
      echo "$runs_json" >&2
      exit 1
    }
    run_id="$(printf '%s' "$runs_json" | jq -r --arg sha "$head_sha" \
      '[.[] | select(.headSha == $sha)] | .[0].databaseId // empty')"
    if [ -z "$run_id" ]; then
      echo "adopt-recheck.sh: no verify.yml run found for branch '$branch' at HEAD ($head_sha)." >&2
      echo "  Push this branch and dispatch one: gh workflow run verify.yml --ref $branch" >&2
      exit 1
    fi
    run_url="$(printf '%s' "$runs_json" | jq -r --arg id "$run_id" '.[] | select(.databaseId == ($id | tonumber)) | .url')"
  else
    run_url="$(gh run view "$run_id" --json url --jq '.url' 2>/dev/null)" || run_url=""
  fi

  work="$(mktemp -d)"
  if ! gh run download "$run_id" --name recheck-record --dir "$work" > "$work/download.log" 2>&1; then
    echo "adopt-recheck.sh: gh run download failed for run $run_id:" >&2
    cat "$work/download.log" >&2
    exit 1
  fi
  if [ -f "$work/recheck.txt" ]; then
    candidate="$work/recheck.txt"
  elif [ -f "$work/recheck.partial.txt" ]; then
    echo "adopt-recheck.sh: run $run_id's recheck-record artifact contains only recheck.partial.txt" >&2
    echo "  (no recheck.txt): that run's recheck job did not produce a complete record. ${run_url:+See $run_url.}" >&2
    exit 1
  else
    echo "adopt-recheck.sh: run $run_id's recheck-record artifact contains neither recheck.txt nor" >&2
    echo "  recheck.partial.txt. ${run_url:+See $run_url.}" >&2
    exit 1
  fi
fi

# ---------------------------------------------------------------------------------- validation
tree_lines="$(identity_digest_lines "$EX")" || {
  echo "adopt-recheck.sh: could not digest this tree's certificate inputs (a listed file is missing)" >&2
  exit 1
}
tree_id="sha256:$(printf '%s\n' "$tree_lines" | identity_of_lines)"

rec_id="$(sed -n -E 's/^certificate identity: (sha256:[0-9a-f]{64})$/\1/p' "$candidate" | head -1)"
if [ -z "$rec_id" ]; then
  echo "adopt-recheck.sh: $candidate has no 'certificate identity:' line; refusing" >&2
  exit 1
fi
if [ "$rec_id" != "$tree_id" ]; then
  echo "adopt-recheck.sh: $candidate is for identity $rec_id, but this tree is $tree_id; refusing" >&2
  echo "  (the record was produced for a different tree than the one checked out here)" >&2
  exit 1
fi
if ! grep -q '^produced on: ' "$candidate"; then
  echo "adopt-recheck.sh: $candidate has no 'produced on:' line; refusing (malformed record)" >&2
  exit 1
fi
if [ -n "$from_file" ]; then
  produced_line="$(sed -n 's/^produced on: //p' "$candidate" | head -1)"
  case "$produced_line" in
    *"$CI_PRODUCER_1"*|*"$CI_PRODUCER_2"*) ;;
    *)
      echo "adopt-recheck.sh: $candidate's 'produced on:' line does not name a CI recheck producer; refusing" >&2
      echo "  found: $produced_line" >&2
      echo "  --from only accepts a record naming '$CI_PRODUCER_1' or '$CI_PRODUCER_2' (verify.yml's RECHECK_PRODUCER_NAME); a locally-produced record cannot be adopted this way." >&2
      exit 1
      ;;
  esac
fi
if ! grep -qx 'record: complete' "$candidate"; then
  reason="$(sed -n 's/^record: //p' "$candidate" | head -1)"
  echo "adopt-recheck.sh: $candidate is not a complete record (${reason:-no 'record:' line}); refusing" >&2
  echo "  A partial record is never adopted as certificate/recheck.txt; see certificate/README.md." >&2
  exit 1
fi
if grep -qE '^verdict: [^ ]+ [^ ]+ FAIL( |$)' "$candidate"; then
  echo "adopt-recheck.sh: $candidate records a FAIL verdict; refusing" >&2
  grep -E '^verdict: [^ ]+ [^ ]+ FAIL( |$)' "$candidate" | sed 's/^/  /' >&2
  exit 1
fi

produced="$(sed -n 's/^produced on: //p' "$candidate" | head -1)"
if $dry_run; then
  echo "adopt-recheck.sh: $candidate is a valid, complete record for this tree ($tree_id)"
  echo "  produced on: $produced"
  [ -n "$run_url" ] && echo "  run: $run_url"
  echo "  --dry-run: certificate/recheck.txt was NOT written"
  exit 0
fi

cp "$candidate" "$RECHECK"
echo "adopt-recheck.sh: adopted $candidate as certificate/recheck.txt"
echo "  identity: $tree_id"
echo "  produced on: $produced"
[ -n "$run_url" ] && echo "  run: $run_url"
echo "  Review the diff and commit it yourself, for example:"
echo "    git -C \"$(cd "$EX/.." && pwd)\" diff -- framed_channel/certificate/recheck.txt"
echo "    git -C \"$(cd "$EX/.." && pwd)\" add framed_channel/certificate/recheck.txt"
echo "    git -C \"$(cd "$EX/.." && pwd)\" commit -m 'certificate: adopt CI-produced recheck.txt'"
