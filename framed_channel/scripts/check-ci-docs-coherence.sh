#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# check-ci-docs-coherence.sh -- structural coherence between docs/ci.md and .github/. READ-ONLY.
#
# docs/ci.md is prose, hand-maintained alongside the workflows it describes, and drifts silently:
# a `timeout-minutes:` bumped in YAML but not in the Timeouts table, a workflow added without a
# Concurrency-paragraph mention, a `paths:` filter edited on push but not pull_request. None of
# that fails CI today. This script encodes twelve structural invariants between docs/ci.md and
# .github/{workflows,actions}/ so that class of drift fails at the commit that introduces it,
# same as check-spdx.sh does for license headers and aeneas-revs.sh/recheck-revs.sh do for
# revision pins.
#
# Design: parse narrowly, per invariant -- never generate docs/ci.md's tables from the workflows
# (would destroy the Summary table's free-form "what green certifies" prose) and never delete the
# duplicated facts (would destroy the page's value as a cross-workflow index). Only invariant 3b
# (paths: vs. the Trigger-policy table) needs more than a direct parse: the table compresses a
# `paths:` list into brace-expansion shorthand, so that one check expands `X/{a,b}/Y` before
# comparing. Counts are never hardcoded: invariant 6 asserts cardinality 1 per action name, and
# invariant 10 compares the doc's own stated number against a computed one, never a literal.
#
# CI-only placement, deliberately: this check is wired into ci.yml's hygiene job, never into
# check.sh or full-gate.sh. check.sh's output feeds the certificate, and verify.yml's `paths:`
# filter deliberately excludes docs/**; making the certificate depend on docs/ci.md would either
# make the gate un-runnable from its declared inputs, or force docs/** into verify.yml's filter,
# which would itself violate invariant 3b (an entry admitting changes the gate does not read).
#
# Invariant 12 is about .github/ itself rather than docs/ci.md: GitHub resolves a repository's
# landing page as .github/README.md, then the root README.md, then docs/README.md, so a README
# in .github/ silently replaces the project's front page. The repository's per-directory README
# convention makes that an easy, invisible mistake -- it happened once, and browsing the rendered
# repository was the only thing that surfaced it.
#
# Non-coverage: invariant 7 (anchors) checks that a docs/ci.md#anchor reference resolves to a
# real heading -- it does NOT check that the referencing sentence's claim matches the anchored
# section's content. The 2026-09-20 review's M1 finding (README.md linking docs/ci.md#platform-matrix
# for Windows/WSL2, when that table has no WSL2 row) was exactly this shape -- a live, correctly
# resolving anchor paired with an incorrect claim -- and this invariant would not have caught it.
# Semantic anchor-content correspondence is a separate, larger check, out of scope for this round.
# Perishable measurement claims (durations, ratios) are also out of scope; the "Measured figures."
# convention documented in docs/ci.md's own header owns that class.
#
# Usage: bash scripts/check-ci-docs-coherence.sh [--root DIR] [-h | --help]
#   --root DIR   the tree to scan (default: the repository root, the parent of framed_channel/)
#
# Requires: bash >= 4.4; grep, awk, sed, find (POSIX-ish). No nix develop, no jq/python/yq.
# Exit: 0 every invariant holds (or is a reasoned [skip]), 1 an invariant is violated, 2 usage error.

set -u

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"

while [ "$#" -gt 0 ]; do
  case "$1" in
    --root)
      [ "$#" -ge 2 ] || { echo "check-ci-docs-coherence.sh: --root needs a directory" >&2; exit 2; }
      ROOT="$2"; shift 2 ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "check-ci-docs-coherence.sh: unknown argument '$1' (expected --root DIR)" >&2
       exit 2 ;;
  esac
done
[ -d "$ROOT" ] || { echo "check-ci-docs-coherence.sh: --root '$ROOT' is not a directory" >&2; exit 2; }
ROOT="$(cd "$ROOT" && pwd)"

WF="$ROOT/.github/workflows"
ACTIONS="$ROOT/.github/actions"
DOC="$ROOT/docs/ci.md"

status=0
ok() { echo "[ok] $*"; }
skip() { echo "[skip] $*"; }
fail() { echo "[FAIL] $*"; status=1; }

# ---------------------------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------------------------

# workflow_files -- every .github/workflows/*.yml basename, one per line, sorted.
workflow_files() {
  find "$WF" -maxdepth 1 -name '*.yml' -exec basename {} \; 2>/dev/null | sort
}

# on_trigger_block FILE TRIGGER -- print the lines of FILE's `on:<TRIGGER>:` block (everything
# indented under it, i.e. 4+ spaces), exclusive of the trigger line itself. Exit 0 if the trigger
# key was found at all (even with an empty block), exit 1 if not -- distinct from whether it
# carries a `paths:` key, which paths_from_block below determines.
on_trigger_block() {
  local f="$1" trig="$2"
  awk -v trig="  ${trig}:" '
    BEGIN { in_on = 0; in_trig = 0; found = 0 }
    /^on:/ { in_on = 1; next }
    in_on && $0 !~ /^[[:space:]]/ { in_on = 0 }
    in_on && index($0, trig) == 1 { in_trig = 1; found = 1; next }
    in_trig && /^  [A-Za-z_]/ { in_trig = 0 }
    in_trig { print }
    END { exit (found ? 0 : 1) }
  ' "$f"
}

# paths_from_block -- reads an on_trigger_block's text on stdin; prints each entry of its
# `paths:` list (quotes stripped, a leading `!` negation kept), one per line, in file order.
# Exit 0 if a `paths:` key was present (even with zero entries), exit 1 if absent.
paths_from_block() {
  awk '
    BEGIN { in_paths = 0; found = 0 }
    /^    paths:/ { in_paths = 1; found = 1; next }
    in_paths && /^    [A-Za-z_]/ { in_paths = 0 }
    in_paths && /^      - / {
      line = $0
      sub(/^      - /, "", line)
      gsub(/^"/, "", line); gsub(/"$/, "", line)
      gsub(/^'"'"'/, "", line); gsub(/'"'"'$/, "", line)
      print line
    }
    END { exit (found ? 0 : 1) }
  '
}

# doc_section NAME -- print the lines of docs/ci.md strictly between the "## NAME" heading and
# the next "## " heading (or EOF), exclusive of both. A requested section that does not exist
# means every comparison depending on it must [skip] with the missing heading named, never
# silently pass -- so callers test this function's exit status (via `if sec="$(doc_section X)";
# then ...`), never assume a non-empty result.
doc_section() {
  local name="$1"
  if [ ! -f "$DOC" ] || ! grep -qxF "## $name" "$DOC"; then
    return 1
  fi
  awk -v want="## $name" '
    $0 == want { infound = 1; next }
    infound && /^## / { exit }
    infound { print }
  ' "$DOC"
}

# word_to_number WORD -- "One".."Twenty" (case-insensitive) or a bare digit string -> its value
# on stdout, exit 1 if WORD is neither.
word_to_number() {
  case "$(tr '[:upper:]' '[:lower:]' <<< "$1")" in
    one) echo 1 ;; two) echo 2 ;; three) echo 3 ;; four) echo 4 ;; five) echo 5 ;;
    six) echo 6 ;; seven) echo 7 ;; eight) echo 8 ;; nine) echo 9 ;; ten) echo 10 ;;
    eleven) echo 11 ;; twelve) echo 12 ;; thirteen) echo 13 ;; fourteen) echo 14 ;;
    fifteen) echo 15 ;; sixteen) echo 16 ;; seventeen) echo 17 ;; eighteen) echo 18 ;;
    nineteen) echo 19 ;; twenty) echo 20 ;;
    [0-9]*) echo "$1" ;;
    *) return 1 ;;
  esac
}

# sha_sites -- print "<action>\t<sha>\t<rel-path>:<lineno>" for every SHA-pinned uses: site under
# .github/{workflows,actions}/, one per line. Shared by invariants 5 and 6 so the discovery
# regex lives in exactly one place.
sha_sites() {
  local f rel lineno match action sha
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    rel="${f#"$ROOT"/}"
    while IFS=: read -r lineno match; do
      action="${match#uses:}"
      action="$(sed -E 's/^[[:space:]]+//; s/@.*$//' <<< "$action")"
      sha="${match##*@}"
      printf '%s\t%s\t%s:%s\n' "$action" "$sha" "$rel" "$lineno"
    done < <(grep -noE 'uses:[[:space:]]*[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(/[A-Za-z0-9_.-]+)*@[0-9a-f]{40}' "$f")
  done < <(find "$WF" "$ACTIONS" -maxdepth 2 -name '*.yml' 2>/dev/null | sort)
}

# ---------------------------------------------------------------------------------------------
# Invariant 5: every uses: <owner>/<repo>@<40-hex sha> carries a trailing "# v..." comment.
# .github/dependabot.yml's own header explains why: Dependabot's github-actions ecosystem moves
# the SHA and the comment together, and needs the comment to already be there.
# ---------------------------------------------------------------------------------------------
invariant_5_sha_comment() {
  local action sha loc rel lineno sites=0 bad=0
  while IFS=$'\t' read -r action sha loc; do
    [ -n "$action" ] || continue
    sites=$((sites + 1))
    rel="${loc%:*}"; lineno="${loc##*:}"
    local line
    line="$(sed -n "${lineno}p" "$ROOT/$rel")"
    if ! grep -qE "@${sha}[[:space:]]*#[[:space:]]*v[0-9]" <<< "$line"; then
      fail "invariant 5: $rel:$lineno: SHA-pinned uses: has no trailing '# vX.Y.Z' comment"
      bad=$((bad + 1))
    fi
  done < <(sha_sites)
  if [ "$sites" -eq 0 ]; then
    skip "invariant 5: no SHA-pinned uses: sites found"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 5: all $sites SHA-pinned uses: sites carry a trailing version comment"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 6: every action name resolves to a single SHA across the whole tree. Asserts
# cardinality 1, never a specific count -- a workflow-deduplication pass already made an earlier
# hand count of "how many sites use this action" stale once; this check must never depend on one.
# ---------------------------------------------------------------------------------------------

# A deliberate two-SHA migration window is recorded here, one entry per exception, never by
# weakening the check itself. Empty today. Shape: "owner/repo|reason".
SHA_EXCEPTIONS=(
)

sha_exception_reason() {
  local a="$1" entry eaction ereason
  for entry in "${SHA_EXCEPTIONS[@]:-}"; do
    [ -n "$entry" ] || continue
    IFS='|' read -r eaction ereason <<< "$entry"
    if [ "$a" = "$eaction" ]; then printf '%s\n' "$ereason"; return 0; fi
  done
  return 1
}

invariant_6_single_sha() {
  local tmp action
  tmp="$(mktemp)"
  sha_sites > "$tmp"

  local actions count=0 bad=0
  actions="$(cut -f1 "$tmp" | sort -u)"
  while IFS= read -r action; do
    [ -n "$action" ] || continue
    count=$((count + 1))
    local shas nsha reason
    shas="$(awk -F'\t' -v a="$action" '$1 == a { print $2 }' "$tmp" | sort -u)"
    nsha="$(wc -l <<< "$shas")"
    if [ "$nsha" -le 1 ]; then continue; fi
    if reason="$(sha_exception_reason "$action")"; then
      skip "invariant 6: $action pins $nsha SHAs ($reason)"
      continue
    fi
    local sites
    sites="$(awk -F'\t' -v a="$action" '$1 == a { print $2" @ "$3 }' "$tmp" | sort -u | paste -sd';' -)"
    fail "invariant 6: $action pinned to $nsha different SHAs: $sites"
    bad=$((bad + 1))
  done <<< "$actions"
  rm -f "$tmp"

  if [ "$count" -eq 0 ]; then
    skip "invariant 6: no SHA-pinned uses: sites found"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 6: all $count distinct action(s) pin a single SHA each"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 4: every workflow with a live `paths:` key (on push or pull_request) lists its own
# file -- a missing self-include is a silent coverage hole of the same shape
# intel-installer-smoke.yml was created to close (its own SHA-bump PR must trigger itself).
# ---------------------------------------------------------------------------------------------
invariant_4_self_inclusion() {
  local f rel base self trig count=0 bad=0
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    rel="${f#"$ROOT"/}"; base="$(basename "$f")"
    self=".github/workflows/$base"
    for trig in push pull_request; do
      local blk paths
      if blk="$(on_trigger_block "$f" "$trig")" && paths="$(paths_from_block <<< "$blk")"; then
        count=$((count + 1))
        if ! grep -qxF "$self" <<< "$paths"; then
          fail "invariant 4: $rel: on.$trig.paths: does not list its own file ($self)"
          bad=$((bad + 1))
        fi
      fi
    done
  done < <(find "$WF" -maxdepth 1 -name '*.yml' | sort)
  if [ "$count" -eq 0 ]; then
    skip "invariant 4: no workflow carries a live paths: key"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 4: every path-filtered on.push/pull_request block lists its own file ($count block(s))"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 3a: a workflow carrying both push and pull_request with a `paths:` key has identical
# lists (same entries, same order) on both. A workflow carrying only one of the two triggers is
# [ok], not [skip] -- the single-trigger fact is named, since it is not itself a mismatch.
# ---------------------------------------------------------------------------------------------
invariant_3a_push_pr_agree() {
  local f rel count=0 bad=0
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    rel="${f#"$ROOT"/}"
    local push_blk pr_blk push_paths pr_paths have_push=false have_pr=false
    if push_blk="$(on_trigger_block "$f" push)" && push_paths="$(paths_from_block <<< "$push_blk")"; then
      have_push=true
    fi
    if pr_blk="$(on_trigger_block "$f" pull_request)" && pr_paths="$(paths_from_block <<< "$pr_blk")"; then
      have_pr=true
    fi
    if ! $have_push && ! $have_pr; then
      continue
    fi
    count=$((count + 1))
    if $have_push && $have_pr; then
      if [ "$push_paths" != "$pr_paths" ]; then
        fail "invariant 3a: $rel: on.push.paths and on.pull_request.paths differ"
        bad=$((bad + 1))
      fi
    elif $have_push; then
      ok "invariant 3a: $rel: only push carries a paths: key (single-trigger, not a mismatch)"
    else
      ok "invariant 3a: $rel: only pull_request carries a paths: key (single-trigger, not a mismatch)"
    fi
  done < <(find "$WF" -maxdepth 1 -name '*.yml' | sort)
  if [ "$count" -eq 0 ]; then
    skip "invariant 3a: no workflow carries a live paths: key on push or pull_request"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 3a: every push/pull_request paths: pair with both triggers agrees"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 1: every .github/workflows/*.yml basename appears in docs/ci.md's Overview, Summary
# and Timeouts sections. A renamed heading makes every comparison depending on it [skip], never
# a silent pass -- the missing heading is named.
# ---------------------------------------------------------------------------------------------
invariant_1_inventory() {
  local ov su ti
  if ! ov="$(doc_section Overview)"; then skip "invariant 1: docs/ci.md has no '## Overview' heading"; return; fi
  if ! su="$(doc_section Summary)"; then skip "invariant 1: docs/ci.md has no '## Summary' heading"; return; fi
  if ! ti="$(doc_section Timeouts)"; then skip "invariant 1: docs/ci.md has no '## Timeouts' heading"; return; fi
  local wf count=0 bad=0
  while IFS= read -r wf; do
    [ -n "$wf" ] || continue
    count=$((count + 1))
    local -a miss=()
    grep -qF "$wf" <<< "$ov" || miss+=("Overview")
    grep -qF "$wf" <<< "$su" || miss+=("Summary")
    grep -qF "$wf" <<< "$ti" || miss+=("Timeouts")
    if [ "${#miss[@]}" -gt 0 ]; then
      fail "invariant 1: $wf missing from docs/ci.md's ${miss[*]} section(s)"
      bad=$((bad + 1))
    fi
  done < <(workflow_files)
  if [ "$count" -eq 0 ]; then
    skip "invariant 1: no workflow files found"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 1: all $count workflows appear in Overview, Summary and Timeouts"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 10: the Overview's "N more workflows run but carry no badge" sentence names the
# right N -- the workflow-file count minus the badged workflows the same section names ("- **CI**
# -> [...]"-shaped bullets). [skip], not a hardcoded default, when the sentence shape is absent.
# ---------------------------------------------------------------------------------------------
invariant_10_workflow_count() {
  local ov
  if ! ov="$(doc_section Overview)"; then
    skip "invariant 10: docs/ci.md has no '## Overview' heading"
    return
  fi
  local sentence word
  sentence="$(grep -oE '[A-Za-z]+ more workflows? run but carry no badge' <<< "$ov" | head -1)"
  if [ -z "$sentence" ]; then
    skip "invariant 10: sentence shape 'N more workflow(s) run but carry no badge' not found in Overview"
    return
  fi
  word="$(awk '{print $1}' <<< "$sentence")"
  local claimed
  if ! claimed="$(word_to_number "$word")"; then
    skip "invariant 10: could not parse the number word '$word' in '$sentence'"
    return
  fi
  local total badged expected
  total=$(workflow_files | wc -l)
  badged=$(grep -cE '^- \*\*[A-Za-z]+\*\* -> \[' <<< "$ov")
  expected=$((total - badged))
  if [ "$claimed" -ne "$expected" ]; then
    fail "invariant 10: Overview claims '$word more workflows' ($claimed) but $total workflow file(s) minus $badged badged = $expected"
  else
    ok "invariant 10: Overview's workflow-count sentence ('$word' = $claimed) matches $total files minus $badged badged"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 2: every literal `timeout-minutes:` value in every workflow matches its docs/ci.md
# Timeouts-table row, including the fresh-clone-canary.yml four-leg matrix (regexed out of its
# fromJSON(...) macos=true branch, in declared order, and compared against the doc cell's
# "N / N / N / N minutes (<systems>)" list in the same order).
# ---------------------------------------------------------------------------------------------

# timeout_sites FILE -- print "<job>|<minutes>" for every literal (non-expression)
# `timeout-minutes:` assignment in FILE, in file order. <job> is empty if the site precedes any
# `jobs:` sub-key (should not happen in a well-formed workflow, but never misattributed either).
timeout_sites() {
  local f="$1"
  awk '
    BEGIN { injobs = 0; job = "" }
    /^jobs:/ { injobs = 1; next }
    injobs && /^  [A-Za-z0-9_-]+:[[:space:]]*$/ {
      line = $0; sub(/^  /, "", line); sub(/:[[:space:]]*$/, "", line); job = line; next
    }
    /timeout-minutes:[[:space:]]*[0-9]+[[:space:]]*$/ {
      n = $0
      sub(/.*timeout-minutes:[[:space:]]*/, "", n)
      sub(/[[:space:]]*$/, "", n)
      print job "|" n
    }
  ' "$f"
}

# canary_timeout_minutes FILE -- the fresh-clone-canary.yml matrix's four `timeout_minutes`
# values from the macos=true (four-leg) fromJSON(...) branch, comma-joined, in declared order.
# Recognizes exactly this file's `&& '[...]' || '[...]'` shape; empty output if not found.
canary_timeout_minutes() {
  local f="$1"
  awk '
    /&&[[:space:]]*.\[/ { active = 1 }
    active && /\|\|[[:space:]]*.\[/ { active = 0 }
    active { print }
  ' "$f" | grep -oE '"timeout_minutes":[0-9]+' | grep -oE '[0-9]+' | paste -sd',' -
}

# timeouts_table_rows -- print "<workflow.yml>|<job-or-empty>|<minutes-csv>" for every row of
# docs/ci.md's Timeouts table, skipping the header and separator rows. <job> is empty for a
# workflow-scoped row (e.g. "`build-and-test.yml` (every caller)"); <minutes-csv> holds every
# integer in the Timeout column in order (one value, or four for the canary's matrix row).
timeouts_table_rows() {
  local sec
  sec="$(doc_section "Timeouts")" || return 1
  awk -F'|' '
    NF < 4 { next }
    {
      col1 = $2; col2 = $3
      gsub(/^[ \t]+|[ \t]+$/, "", col1)
      gsub(/^[ \t]+|[ \t]+$/, "", col2)
    }
    col1 ~ /^-+$/ { next }
    col1 == "Job" { next }
    {
      wf = ""; job = ""
      tmp = col1
      while (match(tmp, /`[^`]*`/)) {
        tok = substr(tmp, RSTART + 1, RLENGTH - 2)
        if (tok ~ /\.yml$/ && wf == "") wf = tok
        else if (job == "" && wf != "") job = tok
        tmp = substr(tmp, RSTART + RLENGTH)
      }
      if (wf == "") next
      idx = index(col2, "minute")
      mtext = (idx > 0) ? substr(col2, 1, idx - 1) : col2
      minutes = ""
      while (match(mtext, /[0-9]+/)) {
        if (minutes != "") minutes = minutes ","
        minutes = minutes substr(mtext, RSTART, RLENGTH)
        mtext = substr(mtext, RSTART + RLENGTH)
      }
      print wf "|" job "|" minutes
    }
  ' <<< "$sec"
}

invariant_2_timeouts() {
  local rows
  if ! rows="$(timeouts_table_rows)"; then
    skip "invariant 2: docs/ci.md has no '## Timeouts' heading"
    return
  fi

  local -A doc_min=() doc_min_bare=()
  local wf job minutes
  while IFS='|' read -r wf job minutes; do
    [ -n "$wf" ] || continue
    if [ -n "$job" ]; then doc_min["$wf|$job"]="$minutes"; else doc_min_bare["$wf"]="$minutes"; fi
  done <<< "$rows"

  local f rel base count=0 bad=0
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    base="$(basename "$f")"
    [ "$base" = "fresh-clone-canary.yml" ] && continue # matrix case, handled separately below
    rel="${f#"$ROOT"/}"
    local jb val key
    while IFS='|' read -r jb val; do
      [ -n "$val" ] || continue
      count=$((count + 1))
      key="$base|$jb"
      if [ -n "${doc_min[$key]:-}" ]; then
        if [ "${doc_min[$key]}" != "$val" ]; then
          fail "invariant 2: $rel ($jb): timeout-minutes: $val, but docs/ci.md's Timeouts row says ${doc_min[$key]}"
          bad=$((bad + 1))
        fi
      elif [ -n "${doc_min_bare[$base]:-}" ]; then
        if [ "${doc_min_bare[$base]}" != "$val" ]; then
          fail "invariant 2: $rel ($jb): timeout-minutes: $val, but docs/ci.md's Timeouts row for $base says ${doc_min_bare[$base]}"
          bad=$((bad + 1))
        fi
      else
        fail "invariant 2: $rel ($jb): timeout-minutes: $val has no matching docs/ci.md Timeouts row"
        bad=$((bad + 1))
      fi
    done < <(timeout_sites "$f")
  done < <(find "$WF" -maxdepth 1 -name '*.yml' | sort)

  local canary="$WF/fresh-clone-canary.yml"
  if [ -f "$canary" ]; then
    local canary_vals doc_canary
    canary_vals="$(canary_timeout_minutes "$canary")"
    doc_canary="${doc_min_bare[fresh-clone-canary.yml]:-}"
    if [ -z "$canary_vals" ]; then
      skip "invariant 2: fresh-clone-canary.yml's four-leg timeout_minutes matrix literal not found"
    elif [ -z "$doc_canary" ]; then
      fail "invariant 2: fresh-clone-canary.yml has no matching docs/ci.md Timeouts row"
      bad=$((bad + 1))
    elif [ "$canary_vals" != "$doc_canary" ]; then
      fail "invariant 2: fresh-clone-canary.yml's matrix timeout_minutes ($canary_vals) does not match docs/ci.md's Timeouts row ($doc_canary)"
      bad=$((bad + 1))
    else
      count=$((count + 1))
    fi
  fi

  if [ "$count" -eq 0 ]; then
    skip "invariant 2: no literal timeout-minutes: site found"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 2: all $count timeout-minutes site(s) (including the canary matrix) match docs/ci.md's Timeouts table"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 3b: for each workflow with a live `paths:` key, its YAML entries match the
# Trigger-policy table's row for it. The table compresses several YAML entries into a
# brace-expansion cell (e.g. `` `framed_channel/{lean,aeneas,rust,scripts,certificate}/**` ``),
# so this is the one invariant that needs more than a direct parse.
# ---------------------------------------------------------------------------------------------

# brace_expand ENTRY -- print ENTRY with a single `{a,b,...}` group expanded into one line per
# alternative, preserving any prefix/suffix around the group (`X/{a,b,c}/Y` and `X/{a,b}.ext` are
# the two shapes docs/ci.md uses). Prints ENTRY unchanged, on one line, if it has no `{` at all.
# Returns 1 (prints nothing) on any other brace syntax -- nested braces, more than one group, an
# unmatched brace, or fewer than two comma-separated alternatives -- never a guessed expansion.
brace_expand() {
  local entry="$1"
  case "$entry" in
    *'{'*) ;;
    *) printf '%s\n' "$entry"; return 0 ;;
  esac
  local nopen nclose
  nopen="$(grep -o '{' <<< "$entry" | wc -l)"
  nclose="$(grep -o '}' <<< "$entry" | wc -l)"
  [ "$nopen" -eq 1 ] && [ "$nclose" -eq 1 ] || return 1
  local prefix group suffix
  prefix="${entry%%\{*}"
  group="${entry#*\{}"; group="${group%%\}*}"
  suffix="${entry#*\}}"
  case "$group" in
    *'{'*|*'}'*|"") return 1 ;;
  esac
  local -a alts
  IFS=',' read -ra alts <<< "$group"
  [ "${#alts[@]}" -ge 2 ] || return 1
  local alt
  for alt in "${alts[@]}"; do
    printf '%s%s%s\n' "$prefix" "$alt" "$suffix"
  done
}

# trigger_policy_col2 WORKFLOW -- the docs/ci.md Trigger-policy table's `paths:` column text for
# WORKFLOW's row (backticks and surrounding whitespace kept, for brace_expand's caller to parse).
# Exit 1 if the Trigger policy heading, or a row for WORKFLOW, is not found.
trigger_policy_col2() {
  local wf="$1" sec
  sec="$(doc_section "Trigger policy")" || return 1
  awk -F'|' -v wf="\`$wf\`" '
    NF < 4 { next }
    {
      col1 = $2; gsub(/^[ \t]+|[ \t]+$/, "", col1)
      if (col1 == wf) {
        col2 = $3; gsub(/^[ \t]+|[ \t]+$/, "", col2)
        print col2; found = 1; exit
      }
    }
    END { exit (found ? 0 : 1) }
  ' <<< "$sec"
}

invariant_3b_trigger_policy() {
  local reason_gate="workflow_dispatch-only; Actions has no path filter on dispatch, and this row is a prose reference to verify.yml's list, not a path list"
  local reason_recheck="workflow_dispatch-only; Actions has no path filter on dispatch; this row documents the job's complete input set, not an active filter"

  local f rel base count=0 bad=0
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    base="$(basename "$f")"
    rel="${f#"$ROOT"/}"

    if [ "$base" = "ci-macos-gate.yml" ]; then
      skip "invariant 3b: $base ($reason_gate)"; continue
    fi
    if [ "$base" = "ci-macos-recheck.yml" ]; then
      skip "invariant 3b: $base ($reason_recheck)"; continue
    fi

    local paths have_paths=false
    local push_blk push_paths pr_blk pr_paths
    if push_blk="$(on_trigger_block "$f" push)" && push_paths="$(paths_from_block <<< "$push_blk")"; then
      have_paths=true; paths="$push_paths"
    elif pr_blk="$(on_trigger_block "$f" pull_request)" && pr_paths="$(paths_from_block <<< "$pr_blk")"; then
      have_paths=true; paths="$pr_paths"
    fi
    $have_paths || continue

    local col2
    if ! col2="$(trigger_policy_col2 "$base")"; then
      fail "invariant 3b: $base has a live paths: key but no docs/ci.md Trigger-policy row"
      bad=$((bad + 1))
      continue
    fi

    local -a doc_tokens=()
    local tok expanded e
    while IFS= read -r tok; do
      [ -n "$tok" ] || continue
      if ! expanded="$(brace_expand "$tok")"; then
        echo "check-ci-docs-coherence.sh: invariant 3b: $base's Trigger-policy cell has an unrecognized brace pattern: '$tok'" >&2
        exit 2
      fi
      while IFS= read -r e; do doc_tokens+=("$e"); done <<< "$expanded"
    done < <(grep -oE '`[^`]*`' <<< "$col2" | sed -E 's/^`//; s/`$//')

    count=$((count + 1))
    local self=".github/workflows/$base" entry norm t found
    while IFS= read -r entry; do
      [ -n "$entry" ] || continue
      norm="${entry#!}"
      [ "$norm" = "$self" ] && continue
      found=false
      for t in "${doc_tokens[@]}"; do
        if [ "$t" = "$norm" ]; then found=true; break; fi
      done
      if ! $found; then
        fail "invariant 3b: $rel: on.paths entry '$entry' has no match in docs/ci.md's Trigger-policy row for $base"
        bad=$((bad + 1))
      fi
    done <<< "$paths"
  done < <(find "$WF" -maxdepth 1 -name '*.yml' | sort)

  if [ "$count" -eq 0 ]; then
    skip "invariant 3b: no workflow with a live paths: key to compare against the Trigger-policy table"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 3b: every filtered workflow's paths: matches its Trigger-policy row ($count workflow(s))"
  fi
}

# ---------------------------------------------------------------------------------------------
# Cross-reference tier: invariants 7 (anchors), 8 (quoted section names) and 9 (workflow/job
# cross-references) all resolve a prose reference against docs/ci.md or a workflow's own
# structure. Scanned files: every non-specs/** *.md file plus .github/workflows/*.yml and
# .github/actions/*/*.yml, matching the audit's finding that this drift class shows up in both
# markdown and workflow-comment prose.
# ---------------------------------------------------------------------------------------------

# prose_files -- every non-specs/** *.md file plus every .github/workflows/*.yml and
# .github/actions/*/*.yml file under ROOT, one per line.
prose_files() {
  find "$ROOT" -path '*/.git' -prune -o -path "$ROOT/specs" -prune -o \
    \( -name '*.md' -o -path '*/.github/workflows/*.yml' -o -path '*/.github/actions/*/*.yml' \) \
    -type f -print 2>/dev/null | sort
}

# github_slugify TEXT -- GitHub's Markdown-heading anchor algorithm: lowercase, strip everything
# but word characters/spaces/hyphens, spaces to hyphens.
github_slugify() {
  local s="$1"
  s="$(tr '[:upper:]' '[:lower:]' <<< "$s")"
  s="$(sed -E 's/[^a-z0-9 -]//g' <<< "$s")"
  s="$(sed -E 's/ /-/g' <<< "$s")"
  printf '%s\n' "$s"
}

# yml_comment_blocks FILE -- print "<startline>\t<joined text>" for each maximal run of
# consecutive `#`-prefixed comment lines in FILE, the `#` and one following space stripped and
# the lines joined with a single space each. A wrapped prose reference like
# `docs/ci.md's "Windows runs on\n# request only"` must be read as one sentence, or the
# quoted-name and job-reference checks below would never see the second half.
yml_comment_blocks() {
  local f="$1"
  awk '
    function flush() { if (start != 0) { print start "\t" buf; buf = ""; start = 0 } }
    /^[[:space:]]*#/ {
      line = $0
      sub(/^[[:space:]]*#[[:space:]]?/, "", line)
      if (start == 0) { start = NR; buf = line } else { buf = buf " " line }
      next
    }
    { flush() }
    END { flush() }
  ' "$f"
}

# ---------------------------------------------------------------------------------------------
# Invariant 7: every `docs/ci.md#<anchor>` reference (any relative path prefix) resolves to a
# real docs/ci.md heading. See the header's Non-coverage note: this does not check that the
# referencing sentence's claim matches the anchored section's content.
# ---------------------------------------------------------------------------------------------
invariant_7_anchors() {
  if [ ! -f "$DOC" ]; then
    skip "invariant 7: docs/ci.md not found"
    return
  fi
  local -A doc_anchors=()
  local heading slug
  while IFS= read -r heading; do
    slug="$(github_slugify "$heading")"
    doc_anchors["$slug"]=1
  done < <(grep -oE '^## .+' "$DOC" | sed -E 's/^## //')

  local f rel count=0 bad=0
  while IFS= read -r f; do
    rel="${f#"$ROOT"/}"
    local lineno match anchor
    while IFS=: read -r lineno match; do
      anchor="${match##*#}"; anchor="${anchor%)}"
      count=$((count + 1))
      if [ -z "${doc_anchors[$anchor]:-}" ]; then
        fail "invariant 7: $rel:$lineno: docs/ci.md#$anchor has no matching heading"
        bad=$((bad + 1))
      fi
    done < <(grep -noE '\]\([^)]*ci\.md#[A-Za-z0-9_-]+\)' "$f")
  done < <(prose_files)

  if [ "$count" -eq 0 ]; then
    skip "invariant 7: no docs/ci.md#anchor reference sites found"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 7: all $count docs/ci.md#anchor reference site(s) resolve to a real heading"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 8: every quoted `docs/ci.md's "<Name>"` reference names a real '## <Name>' heading.
# Only the quoted form is checkable; an unquoted reference (`docs/ci.md's Cost section has the
# measured figures`) runs into surrounding prose and is counted, never FAILed.
# ---------------------------------------------------------------------------------------------
invariant_8_quoted_sections() {
  if [ ! -f "$DOC" ]; then
    skip "invariant 8: docs/ci.md not found"
    return
  fi
  local -A headings=()
  local h
  while IFS= read -r h; do headings["$h"]=1; done < <(grep -oE '^## .+' "$DOC" | sed -E 's/^## //')

  local f rel count=0 bad=0 unquoted=0
  while IFS= read -r f; do
    rel="${f#"$ROOT"/}"
    local startline text q name u
    while IFS=$'\t' read -r startline text; do
      [ -n "$text" ] || continue
      while IFS= read -r q; do
        [ -n "$q" ] || continue
        name="${q#*\"}"; name="${name%\"}"
        count=$((count + 1))
        if [ -z "${headings[$name]:-}" ]; then
          fail "invariant 8: $rel:$startline: docs/ci.md's \"$name\" has no matching '## $name' heading"
          bad=$((bad + 1))
        fi
      done < <(grep -oE "ci\.md.s \"[^\"]+\"" <<< "$text")
    done < <(yml_comment_blocks "$f")
    u=$(grep -coE "ci\.md.s [A-Z][A-Za-z]*( [A-Za-z]+)* section" "$f" 2>/dev/null)
    [ -n "$u" ] || u=0
    unquoted=$((unquoted + u))
  done < <(prose_files)

  [ "$unquoted" -gt 0 ] && skip "invariant 8: $unquoted unquoted docs/ci.md's <Name> section reference(s) (unquoted forms are not checked)"
  if [ "$count" -eq 0 ]; then
    skip "invariant 8: no quoted docs/ci.md's \"Name\" reference found"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 8: all $count quoted docs/ci.md's \"Name\" reference(s) match a real heading"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 9: every ``X.yml's `job` job`` reference names a real job of X.yml -- the audit's
# "header comments naming a job in the wrong workflow" instance.
# ---------------------------------------------------------------------------------------------
invariant_9_job_refs() {
  local re='([A-Za-z0-9_./-]*[A-Za-z0-9_.-]+\.yml)`?.s `([A-Za-z0-9_-]+)`\ job'
  local f rel count=0 bad=0
  while IFS= read -r f; do
    rel="${f#"$ROOT"/}"
    local lineno=0 line
    while IFS= read -r line || [ -n "$line" ]; do
      lineno=$((lineno + 1))
      local remaining="$line" wf job wfbase target whole
      while [[ "$remaining" =~ $re ]]; do
        wf="${BASH_REMATCH[1]}"; job="${BASH_REMATCH[2]}"; whole="${BASH_REMATCH[0]}"
        wfbase="$(basename "$wf")"
        count=$((count + 1))
        target="$WF/$wfbase"
        if [ ! -f "$target" ]; then
          fail "invariant 9: $rel:$lineno: references $wfbase, which does not exist under .github/workflows/"
          bad=$((bad + 1))
        elif ! grep -qE "^  ${job}:[[:space:]]*\$" "$target"; then
          fail "invariant 9: $rel:$lineno: $wfbase has no \`$job\` job (referenced as \`${wfbase}\`'s \`${job}\` job)"
          bad=$((bad + 1))
        fi
        remaining="${remaining#*"$whole"}"
      done
    done < "$f"
  done < <(prose_files)

  if [ "$count" -eq 0 ]; then
    skip "invariant 9: no \`workflow.yml\`'s \`job\` job reference found"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 9: all $count workflow/job cross-reference(s) resolve to a real job"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 11: every workflow carrying a `concurrency:` key is named in docs/ci.md's
# "**Concurrency**:" paragraph, and every workflow named there has a `concurrency:` key.
# ---------------------------------------------------------------------------------------------

# concurrency_paragraph -- print the lines of docs/ci.md's "**Concurrency**:" paragraph (from
# that marker to the next blank line, inclusive of the marker line). Exit 1 if not found.
concurrency_paragraph() {
  [ -f "$DOC" ] || return 1
  grep -q '^\*\*Concurrency\*\*:' "$DOC" || return 1
  awk '
    /^\*\*Concurrency\*\*:/ { active = 1 }
    active && /^$/ { exit }
    active { print }
  ' "$DOC"
}

invariant_11_concurrency_roster() {
  local para
  if ! para="$(concurrency_paragraph)"; then
    skip "invariant 11: docs/ci.md has no '**Concurrency**:' paragraph"
    return
  fi

  local f base count=0 bad=0
  local -a conc_workflows=()
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    base="$(basename "$f")"
    if grep -qE '^concurrency:' "$f"; then
      conc_workflows+=("$base")
      count=$((count + 1))
      if ! grep -qF "$base" <<< "$para"; then
        fail "invariant 11: $base carries a concurrency: block but is not named in docs/ci.md's Concurrency paragraph"
        bad=$((bad + 1))
      fi
    fi
  done < <(find "$WF" -maxdepth 1 -name '*.yml' | sort)

  local named w is_member
  while IFS= read -r named; do
    [ -n "$named" ] || continue
    is_member=false
    for w in "${conc_workflows[@]}"; do [ "$w" = "$named" ] && { is_member=true; break; }; done
    if ! $is_member; then
      fail "invariant 11: docs/ci.md's Concurrency paragraph names $named, which has no concurrency: block"
      bad=$((bad + 1))
    fi
  done < <(grep -oE '`[A-Za-z0-9_.-]+\.yml`' <<< "$para" | tr -d '`' | sort -u)

  if [ "$count" -eq 0 ]; then
    skip "invariant 11: no workflow carries a concurrency: block"
  elif [ "$bad" -eq 0 ]; then
    ok "invariant 11: docs/ci.md's Concurrency paragraph names exactly the $count workflow(s) with a concurrency: block"
  fi
}

# ---------------------------------------------------------------------------------------------
# Invariant 12: .github/ contains no README.md, which GitHub would render as the repository's
# front page in preference to the root README.md.
# ---------------------------------------------------------------------------------------------

invariant_12_no_github_readme() {
  local gh_dir="$ROOT/.github"
  if [ ! -d "$gh_dir" ]; then
    skip "invariant 12: no .github/ directory"
    return
  fi

  # Case-insensitively, since GitHub's own resolution is not case-sensitive here.
  local found=0 f base
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    base="$(basename "$f")"
    fail "invariant 12: .github/$base shadows the root README.md as the repository front page; rename it (see .github/CONTENTS.md)"
    found=$((found + 1))
  done < <(find "$gh_dir" -maxdepth 1 -type f -iname 'README*' 2>/dev/null | sort)

  [ "$found" -eq 0 ] && ok "invariant 12: .github/ has no README, so the root README.md remains the front page"
  return 0
}

main() {
  invariant_5_sha_comment
  invariant_6_single_sha
  invariant_4_self_inclusion
  invariant_3a_push_pr_agree
  invariant_1_inventory
  invariant_10_workflow_count
  invariant_2_timeouts
  invariant_3b_trigger_policy
  invariant_7_anchors
  invariant_8_quoted_sections
  invariant_9_job_refs
  invariant_11_concurrency_roster
  invariant_12_no_github_readme

  if [ "$status" -eq 0 ]; then
    echo "[ok] check-ci-docs-coherence: all invariants hold"
  fi
  exit "$status"
}

main
