#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# approve.sh -- review, then record, approvals of the selection and of Challenge modules.
#
# Two steps. `--review` writes one review file (no terminal needed): a decisions block with every
# item set to "no", the selection draft, and the evidence (digests, diffs since the last approval,
# the candidate table, each Challenge module's text). A person, or an agent assisting them, reads
# it, edits the draft and marks items "yes". `--record` re-computes every digest, refuses if any
# item changed since the review and writes those records to certificate/approvals.yaml: by a
# person, after one typed confirmation on the terminal (by: person); or, with --agent, by an agent,
# with no terminal, when the review's Notes section records its findings (by: agent). It never
# commits. Process and limits: certificate/README.md.
#
# Usage: bash approve.sh --review (--core-only | --aeneas) [--out FILE] [--selection]
#                        [--spec MODULE]... [--all]
#        bash approve.sh --record FILE --approver "Name <email>" (--core-only | --aeneas)
#        bash approve.sh --record FILE --approver "Name (agent) <email>" --agent [...]
#   --review                   write a review file; by default covers every absent or stale item
#   --out FILE                 where to write it (default: a new file under ${TMPDIR:-/tmp})
#   --selection, --spec MODULE, --all
#                              review these items instead (current ones included)
#   --record FILE              record the items marked "yes" in a reviewed file
#   --approver "Name <email>"  who approves (required with --record); an agent's name ends "(agent)"
#   --agent                    record as an agent: no terminal, Notes required, by: agent
#   --core-only, --aeneas      leave out, or require, the bridge package (as spec-check.sh); one
#                              of the two is required, in both --review and --record
#
# Requires: bash >= 4.4, git, column, what spec-check.sh requires; --record without --agent also
# a terminal.
# Exit: 0 written or recorded, 1 not confirmed or a check failed, 2 usage error, no terminal or
# missing prerequisite.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
APPROVALS="$EX/certificate/approvals.yaml"
CANDIDATES="$EX/certificate/candidates.txt"
# shellcheck source=scripts/lib/approval-digests.sh
. "$EX/scripts/lib/approval-digests.sh"
# shellcheck source=scripts/lib/packages.sh
. "$EX/scripts/lib/packages.sh"

mode=""
out=""
record_file=""
approver=""
do_selection=false
spec_modules=()
do_all=false
agent=false
scope_args=()
usage_error() { echo "approve.sh: $* (try --help)" >&2; exit 2; }
while [ "$#" -gt 0 ]; do
  case "$1" in
    --review) mode=review; shift ;;
    --record)
      [ "$#" -ge 2 ] || usage_error "--record needs a review file"
      mode=record; record_file="$2"; shift 2 ;;
    --out)
      [ "$#" -ge 2 ] || usage_error "--out needs a file"
      out="$2"; shift 2 ;;
    --approver)
      [ "$#" -ge 2 ] || usage_error "--approver needs \"Name <email>\""
      approver="$2"; shift 2 ;;
    --selection) do_selection=true; shift ;;
    --spec)
      [ "$#" -ge 2 ] || usage_error "--spec needs a Challenge module name"
      spec_modules+=("$2"); shift 2 ;;
    --all) do_all=true; shift ;;
    --agent) agent=true; shift ;;
    --core-only|--aeneas)
      bridge_scope_arg approve.sh "$1" || exit $?
      scope_args+=("$1"); shift ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) usage_error "unknown argument '$1'" ;;
  esac
done
[ -n "$mode" ] || usage_error "give --review or --record FILE"
[ -n "${bridge_scope:-}" ] || usage_error "give --core-only or --aeneas: neither infers a default any more"
if [ "$mode" = record ]; then
  if $do_selection || $do_all || [ ${#spec_modules[@]} -gt 0 ] || [ -n "$out" ]; then
    usage_error "--record takes its items from the review file; drop --selection/--spec/--all/--out"
  fi
  # A person at a terminal, or a declared agent; named either way.
  if ! $agent && ! { exec 3< /dev/tty; } 2> /dev/null; then
    echo "approve.sh: refusing: no controlling terminal to read a confirmation from." >&2
    echo "  Run --record from an interactive terminal, or record as an agent with --agent." >&2
    exit 2
  fi
  if [ -z "$approver" ]; then
    echo "approve.sh: refusing: --approver \"Name <email>\" is required" >&2
    exit 2
  fi
  if ! approver_valid "$approver"; then
    echo "approve.sh: refusing: --approver must be of the form \"Name <email>\"" >&2
    exit 2
  fi
  by=person
  $agent && by=agent
  if ! approver_matches_by "$approver" "$by"; then
    if $agent; then
      echo "approve.sh: refusing: with --agent the approver is named \"Name (agent) <email>\"" >&2
    else
      echo "approve.sh: refusing: an \"(agent)\" approver records with --agent" >&2
    fi
    exit 2
  fi
  [ -f "$record_file" ] || { echo "approve.sh: $record_file does not exist" >&2; exit 2; }
else
  [ -z "$approver" ] && ! $agent || usage_error "--approver and --agent belong to --record"
  if $do_all && { $do_selection || [ ${#spec_modules[@]} -gt 0 ]; }; then
    usage_error "--all already covers the selection and every module; drop --selection/--spec"
  fi
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# The existing records, parsed (an unparsable file is not silently replaced).
if [ -f "$APPROVALS" ]; then
  if ! approvals_normalize "$APPROVALS" > "$work/records"; then
    grep '^parse-error' "$work/records" >&2
    echo "approve.sh: $APPROVALS does not have the recorded shape; fix it by hand first" >&2
    exit 1
  fi
else
  : > "$work/records"
fi

# spec_check: current digests (and reached items) into $work/spec.
spec_check() {
  echo "Computing the current specification digests (spec-check.sh)..." >&2
  if ! bash "$EX/scripts/spec-check.sh" "${scope_args[@]}" > "$work/spec" 2> "$work/spec.err"; then
    cat "$work/spec.err" >&2
    echo "approve.sh: spec-check.sh failed; nothing was done" >&2
    exit 1
  fi
  if grep -q ' IMPURE ' "$work/spec"; then
    grep ' IMPURE ' "$work/spec" >&2
    echo "approve.sh: a Challenge module is not statement-only; nothing was done" >&2
    exit 1
  fi
}
current_digest() { awk -v m="$1" '$2 == "digest" && $3 == m { print $4 }' "$work/spec"; }
recorded_digest() {
  local i
  i="$(awk -F'\t' -v m="$1" '$1 == "spec" && $3 == "challenge" && $4 == m { print $2 }' "$work/records" | head -1)"
  [ -n "$i" ] || return 0
  awk -F'\t' -v i="$i" '$1 == "spec" && $2 == i && $3 == "spec_digest" { print $4 }' "$work/records"
}
recorded_sel() { awk -F'\t' -v k="$1" '$1 == "sel" && $2 == k { print $3 }' "$work/records"; }

# ------------------------------------------------------------------------------------- review
if [ "$mode" = review ]; then
  spec_check
  src="$(source_sha256 "$EX")" || { echo "approve.sh: cannot digest rust/" >&2; exit 1; }
  cand="$(candidates_sha256 "$EX")" || { echo "approve.sh: certificate/candidates.txt is missing" >&2; exit 1; }
  if ! $do_selection && ! $do_all && [ ${#spec_modules[@]} -eq 0 ]; then
    # Default: every absent or stale item.
    if [ "$(recorded_sel source_sha256)" != "$src" ] || [ "$(recorded_sel candidates_sha256)" != "$cand" ]; then
      do_selection=true
    fi
    while read -r m d; do
      [ "$(recorded_digest "$m")" = "$d" ] || spec_modules+=("$m")
    done < <(awk '$2 == "digest" { print $3, $4 }' "$work/spec")
  elif $do_all; then
    do_selection=true
    mapfile -t spec_modules < <(awk '$2 == "digest" { print $3 }' "$work/spec")
  fi
  for m in "${spec_modules[@]}"; do
    [ -n "$(current_digest "$m")" ] && challenge_file "$m" > /dev/null ||
      { echo "approve.sh: $m is not a Challenge module of a checked package (see spec-check.sh)" >&2; exit 1; }
  done
  if ! $do_selection && [ ${#spec_modules[@]} -eq 0 ]; then
    echo "approve.sh: every approval is current; nothing to review"
    exit 0
  fi
  [ -n "$out" ] || out="$(mktemp "${TMPDIR:-/tmp}/approvals-review.XXXXXX.md")"

  # diff_since DIGEST PATHS...: the diff since the commit that recorded DIGEST, or a note.
  diff_since() {
    local digest="$1" c d
    shift
    if [ -z "$digest" ]; then
      echo "(never approved: review the full text)"
    elif c="$(approval_commit "$digest" "$EX")" && [ -n "$c" ]; then
      d="$(git -C "$EX" diff "$c" -- "$@")"
      if [ -n "$d" ]; then
        printf 'Changes since commit %s, which recorded the last approval:\n\n```diff\n%s\n```\n' "$c" "$d"
      else
        echo "(no diff is available since commit $c, which recorded the last approval: the change is"
        echo "part of that commit's history; review the full text)"
      fi
    else
      echo "(the last approval is not committed; no diff is available: review the full text)"
    fi
  }

  bridge_checked=false
  grep -q '^bridge ' "$work/spec" && bridge_checked=true
  {
    echo "# Approval review"
    echo
    echo "Generated by \`approve.sh --review\` on $(date -u +%Y-%m-%d) for the tree at $(git -C "$EX" rev-parse --short HEAD 2>/dev/null || echo unknown)."
    echo "Read the evidence below. To approve an item, change its \"no\" to \"yes\" in Decisions (edit"
    echo "nothing else on those lines), and adjust the selection draft if needed. Then record it, as a"
    echo "person at a terminal or as an agent (which must first write its findings under Notes):"
    echo
    echo '```'
    echo "bash framed_channel/approve.sh --record $out --approver \"Name <email>\"${scope_args[*]:+ ${scope_args[*]}}"
    echo "bash framed_channel/approve.sh --record $out --approver \"Name (agent) <email>\" --agent${scope_args[*]:+ ${scope_args[*]}}"
    echo '```'
    echo
    echo "## Notes"
    echo
    echo "(The reviewer's findings: what was compared and why each marked item is right. Required for"
    echo "--agent. Not written to approvals.yaml; keep the review file if the reasoning should be kept.)"
    echo
    echo "## Decisions"
    echo
    echo '```'
    $do_selection && echo "no  selection  candidates_sha256=$cand  source_sha256=$src"
    for m in "${spec_modules[@]}"; do
      echo "no  spec  $m  spec_digest=$(current_digest "$m")"
    done
    echo '```'
    if $do_selection; then
      echo
      echo "## Selection draft"
      echo
      if $bridge_checked; then
        echo "Pre-filled: selected = candidates some registered statement is about; declined = the rest."
      else
        echo "Pre-filled: selected = non-derived candidates; declined = derived impls (bridge not checked)."
      fi
      echo "Keep each in-subset candidate under \`selected\`, or under \`declined\` as \`name: reason\`."
      echo
      echo '```yaml'
      insubset_candidates "$CANDIDATES" --with-derived > "$work/insubset"
      awk '$1 == "bridge" && $2 == "reached" { print $3 }' "$work/spec" | LC_ALL=C sort -u > "$work/reached"
      echo "selected:"
      while IFS=$'\t' read -r name derived; do
        if $bridge_checked; then
          grep -qxF "$name" "$work/reached" && echo "  - $name"
        else
          [ "$derived" = "-" ] && echo "  - $name"
        fi
      done < "$work/insubset"
      echo "declined:"
      while IFS=$'\t' read -r name derived; do
        if $bridge_checked; then
          grep -qxF "$name" "$work/reached" && continue
        else
          [ "$derived" = "-" ] && continue
        fi
        if [ "$derived" != "-" ]; then
          echo "  - $name: ${derived#derived:} impl generated by #[derive]; no behavioral claim is made about it"
        else
          echo "  - $name: no registered statement is about it"
        fi
      done < "$work/insubset"
      echo '```'
      echo
      echo "## Evidence: selection"
      echo
      echo "- candidates_sha256: \`$cand\`"
      echo "- source_sha256: \`$src\`"
      echo
      diff_since "$(recorded_sel candidates_sha256)" certificate/candidates.txt rust/src rust/Cargo.toml rust/Cargo.lock
      echo
      echo "Candidates (\`certificate/candidates.txt\`):"
      echo
      echo '```'
      column -t -s $'\t' < "$CANDIDATES"
      echo '```'
    fi
    for m in "${spec_modules[@]}"; do
      rel="$(challenge_file "$m")"
      imports="$(imported_defs "$rel")"
      echo
      echo "## Evidence: $m"
      echo
      echo "- file: \`framed_channel/$rel\`"
      echo "- spec_digest: \`$(current_digest "$m")\` (recorded: \`$(recorded_digest "$m")\`)"
      [ -n "$imports" ] && echo "- definitions imports: $(echo $imports | sed 's/ /, /g')"
      echo
      # shellcheck disable=SC2086
      diff_since "$(recorded_digest "$m")" "$rel" $imports
      echo
      echo '```lean'
      cat "$EX/$rel"
      echo '```'
    done
  } > "$out"
  echo "approve.sh: wrote $out"
  $do_selection && echo "  selection"
  for m in "${spec_modules[@]}"; do echo "  $m"; done
  echo "Review it, mark items \"yes\", then record (a person at a terminal, or an agent with --agent):"
  echo "  bash $EX/approve.sh --record $out --approver \"Name <email>\"${scope_args[*]:+ ${scope_args[*]}}"
  exit 0
fi

# ------------------------------------------------------------------------------------- record
# The Decisions block: the fenced lines after "## Decisions".
awk '
  /^## / { sec = $0; next }
  sec == "## Decisions" && /^```/ { f = !f; next }
  sec == "## Decisions" && f && NF { print }
' "$record_file" > "$work/decisions"
awk '
  /^## / { sec = $0; next }
  sec == "## Selection draft" && /^```/ { f = !f; next }
  sec == "## Selection draft" && f { print }
' "$record_file" > "$work/draft"

bad=0
sel_yes=false
spec_yes=()
declare -A spec_digest_of
while read -r verdict kind a b; do
  case "$verdict" in yes|no) ;; *) echo "approve.sh: decision is not yes/no: $verdict $kind $a $b" >&2; bad=1; continue ;; esac
  case "$kind" in
    selection)
      [ "$verdict" = yes ] || continue
      sel_yes=true
      rev_cand="${a#candidates_sha256=}"; rev_src="${b#source_sha256=}" ;;
    spec)
      [ "$verdict" = yes ] || continue
      spec_yes+=("$a"); spec_digest_of["$a"]="${b#spec_digest=}" ;;
    *) echo "approve.sh: unknown decision line: $verdict $kind $a $b" >&2; bad=1 ;;
  esac
done < "$work/decisions"
[ "$bad" -eq 0 ] || { echo "approve.sh: the Decisions block is malformed; nothing was recorded" >&2; exit 1; }
if ! $sel_yes && [ ${#spec_yes[@]} -eq 0 ]; then
  echo "approve.sh: no item is marked \"yes\" in $record_file; nothing was recorded" >&2
  exit 1
fi
if $agent; then
  notes="$(awk '/^## / { sec = $0; next } sec == "## Notes" && NF && !/^\(The reviewer/ && !/^--agent\. Not written/' "$record_file")"
  if [ -z "$notes" ]; then
    echo "approve.sh: refusing: --agent needs the reviewer's findings under ## Notes; nothing was recorded" >&2
    exit 1
  fi
fi

# Every approved item must still be what was reviewed.
if $sel_yes; then
  src="$(source_sha256 "$EX")" || { echo "approve.sh: cannot digest rust/" >&2; exit 1; }
  cand="$(candidates_sha256 "$EX")" || { echo "approve.sh: certificate/candidates.txt is missing" >&2; exit 1; }
  if [ "$src" != "$rev_src" ] || [ "$cand" != "$rev_cand" ]; then
    echo "approve.sh: refusing: the Rust or the candidate set changed since the review was written; review again" >&2
    bad=1
  fi
  awk '
    /^[ \t]*#/ || /^[ \t]*$/ { next }
    /^selected:/ { s = "sel"; next }
    /^declined:/ { s = "dec"; next }
    s == "sel" && /^  - / { n = $0; sub(/^  - /, "", n); sub(/[ \t]+$/, "", n); print "sel\tselected\t" n; next }
    s == "dec" && /^  - / { l = $0; sub(/^  - /, "", l); i = index(l, ":"); if (i == 0) { print "bad\t" $0; next }
                            n = substr(l, 1, i - 1); r = substr(l, i + 1); sub(/^[ \t]+/, "", r)
                            print "sel\tdeclined\t" n "\t" r; next }
    { print "bad\t" $0 }
  ' "$work/draft" > "$work/decision"
  if grep -q '^bad' "$work/decision"; then
    grep '^bad' "$work/decision" | cut -f2- >&2
    echo "approve.sh: the selection draft has lines of an unknown shape" >&2
    bad=1
  elif ! grep -q '^sel	selected	' "$work/decision"; then
    echo "approve.sh: the selection draft selects nothing" >&2
    bad=1
  fi
fi
if [ ${#spec_yes[@]} -gt 0 ]; then
  spec_check
  for m in "${spec_yes[@]}"; do
    now="$(current_digest "$m")"
    if [ -z "$now" ]; then
      echo "approve.sh: $m is not a Challenge module of a checked package" >&2
      bad=1
    elif [ "$now" != "${spec_digest_of[$m]}" ]; then
      echo "approve.sh: refusing: $m changed since the review (reviewed ${spec_digest_of[$m]}, now $now); review again" >&2
      bad=1
    fi
  done
fi
[ "$bad" -eq 0 ] || { echo "approve.sh: nothing was recorded" >&2; exit 1; }

today="$(date -u +%Y-%m-%d)"
{
  echo
  echo "== Record approvals =="
  echo "approver: $approver ($by)"
  echo "date:     $today"
  echo "review:   $record_file"
  if $sel_yes; then
    echo "  selection: $(grep -c '	selected	' "$work/decision") selected, $(grep -c '	declined	' "$work/decision") declined"
  fi
  for m in "${spec_yes[@]}"; do echo "  $m (spec_digest ${spec_digest_of[$m]})"; done
} > "$work/summary"
if $agent; then
  cat "$work/summary"
else
  cat "$work/summary" > /dev/tty
  printf '\nType "yes" to record these approvals as %s (anything else aborts): ' "$approver" > /dev/tty
  IFS= read -r answer <&3 || answer=""
  if [ "$answer" != yes ]; then
    echo "approve.sh: not confirmed; nothing was recorded" >&2
    exit 1
  fi
fi

if $sel_yes; then
  {
    grep -v '^sel	' "$work/records"
    printf 'sel\tcandidates_sha256\t%s\n' "$cand"
    printf 'sel\tsource_sha256\t%s\n' "$src"
    cat "$work/decision"
    printf 'sel\tapprover\t%s\n' "$approver"
    printf 'sel\tby\t%s\n' "$by"
    printf 'sel\tdate\t%s\n' "$today"
  } > "$work/records.new"
  mv "$work/records.new" "$work/records"
fi
for m in "${spec_yes[@]}"; do
  old="$(awk -F'\t' -v m="$m" '$1 == "spec" && $3 == "challenge" && $4 == m { print $2 }' "$work/records" | head -1)"
  if [ -n "$old" ]; then
    awk -F'\t' -v i="$old" '!($1 == "spec" && $2 == i)' "$work/records" > "$work/records.new"
    idx="$old"
  else
    cp "$work/records" "$work/records.new"
    idx=$(( $(awk -F'\t' '$1 == "spec" { print $2 }' "$work/records" | sort -n | tail -1 | grep . || echo 0) + 1 ))
  fi
  {
    cat "$work/records.new"
    printf 'spec\t%s\tchallenge\t%s\n' "$idx" "$m"
    printf 'spec\t%s\tspec_digest\t%s\n' "$idx" "${spec_digest_of[$m]}"
    printf 'spec\t%s\tapprover\t%s\n' "$idx" "$approver"
    printf 'spec\t%s\tby\t%s\n' "$idx" "$by"
    printf 'spec\t%s\tdate\t%s\n' "$idx" "$today"
  } > "$work/records"
done

# Regenerate certificate/approvals.yaml from $work/records, in the recorded shape.
tmp="$work/approvals.new"
{
  echo "# framed_channel approvals: recorded with approve.sh by a person or a declared agent (by:);"
  echo "# never edited by the gate. scripts/check-approvals.sh verifies each record against the current tree."
  if grep -q '^sel	' "$work/records"; then
    echo "selection:"
    for k in candidates_sha256 source_sha256; do
      awk -F'\t' -v k="$k" '$1 == "sel" && $2 == k { print "  " k ": " $3 }' "$work/records"
    done
    echo "  selected:"
    awk -F'\t' '$1 == "sel" && $2 == "selected" { print "    - " $3 }' "$work/records"
    echo "  declined:"
    awk -F'\t' '$1 == "sel" && $2 == "declined" { gsub(/"/, "\x27", $4); print "    - name: " $3; print "      reason: \"" $4 "\"" }' "$work/records"
    awk -F'\t' '$1 == "sel" && $2 == "approver" { print "  approver: \"" $3 "\"" }' "$work/records"
    awk -F'\t' '$1 == "sel" && $2 == "by" { print "  by: " $3 }' "$work/records"
    awk -F'\t' '$1 == "sel" && $2 == "date" { print "  date: " $3 }' "$work/records"
  fi
  if grep -q '^spec	' "$work/records"; then
    echo "specification:"
    awk -F'\t' '$1 == "spec" { print $2 "\t" $3 "\t" $4 }' "$work/records" |
      awk -F'\t' '
        { v[$1, $2] = $3; if (!($1 in seen)) { seen[$1] = 1; order[++n] = $1 } }
        END {
          for (j = 1; j <= n; j++) {
            i = order[j]
            print "  - challenge: " v[i, "challenge"]
            print "    spec_digest: " v[i, "spec_digest"]
            print "    approver: \"" v[i, "approver"] "\""
            print "    by: " v[i, "by"]
            print "    date: " v[i, "date"]
          }
        }'
  fi
} > "$tmp"
if ! approvals_normalize "$tmp" > /dev/null; then
  echo "approve.sh: internal error: the regenerated file does not parse; nothing was written" >&2
  exit 1
fi
mv "$tmp" "$APPROVALS"
echo "approve.sh: recorded $( $sel_yes && echo "the selection and " )${#spec_yes[@]} specification approval(s) in certificate/approvals.yaml (not committed)"
echo "Check: bash $EX/scripts/check-approvals.sh $APPROVALS ${scope_args[*]}"
