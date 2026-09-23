#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# recheck-record.sh -- render the independent recheck's verdicts and write certificate/recheck.txt
# (or certificate/recheck.partial.txt, when the record is not complete).
#
# Reads recheck-comparator.sh's and recheck-kernel.sh's already-written verdict/deviation files
# from WORK-DIR (their own --out directory), prints one [ok]/[skip]/[FAIL] line per verdict, then
# writes the full record (tool revisions, revision coherence, sandbox deviations, hardening,
# Comparator's assumptions, and the verdicts themselves) to COMPLETE-OUT when the record is
# complete, otherwise to PARTIAL-OUT. Shared by check.sh --recheck and
# .github/workflows/ci-macos-recheck.yml, which runs it standalone over the two scripts' outputs
# so a macOS record (necessarily PARTIAL: Comparator is Linux-only) is byte-identical in shape to
# check.sh's own.
#
# Usage: bash scripts/recheck-record.sh --work-dir DIR --coherence-file FILE --identity IDENTITY
#                                        --complete-out FILE --partial-out FILE [-h | --help]
#   --work-dir DIR        recheck-comparator.sh/recheck-kernel.sh's --out directory: reads
#                          DIR/comparator.verdicts, DIR/kernel.verdicts, DIR/comparator.deviations
#   --coherence-file FILE  recheck_rev_coherence's captured output (printed verbatim into the
#                          record's "revision coherence" section)
#   --identity IDENTITY   the certificate identity (sha256:<hex>) this record is for
#   --complete-out FILE   where to write a complete record
#   --partial-out FILE    where to write a PARTIAL record (some non-lean4lean-fresh verdict is
#                          NOT-RUN)
#
# Requires: bash >= 4.4, awk, coreutils; scripts/lib/recheck-revs.sh (sourced, for
# recheck_record_completeness, recheck_produced_on, recheck_tool_revisions and the constants
# recheck_tool_revisions itself needs).
# Exit: 0 a complete record with no FAIL verdict was written, 1 at least one verdict is FAIL
# (written to whichever of COMPLETE-OUT/PARTIAL-OUT the completeness selects, same as a pass), 2
# a PARTIAL (not complete) record with no FAIL verdict was written, 3 usage error.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [ -z "${_RECHECK_REVS_SOURCED:-}" ]; then
  # shellcheck source=lib/recheck-revs.sh
  . "$EX/scripts/lib/recheck-revs.sh"
fi

work_dir=""
coherence_file=""
identity=""
complete_out=""
partial_out=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --work-dir) [ "$#" -ge 2 ] || { echo "recheck-record.sh: --work-dir needs a directory" >&2; exit 3; }; work_dir="$2"; shift 2 ;;
    --coherence-file) [ "$#" -ge 2 ] || { echo "recheck-record.sh: --coherence-file needs a file" >&2; exit 3; }; coherence_file="$2"; shift 2 ;;
    --identity) [ "$#" -ge 2 ] || { echo "recheck-record.sh: --identity needs sha256:<hex>" >&2; exit 3; }; identity="$2"; shift 2 ;;
    --complete-out) [ "$#" -ge 2 ] || { echo "recheck-record.sh: --complete-out needs a file" >&2; exit 3; }; complete_out="$2"; shift 2 ;;
    --partial-out) [ "$#" -ge 2 ] || { echo "recheck-record.sh: --partial-out needs a file" >&2; exit 3; }; partial_out="$2"; shift 2 ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "recheck-record.sh: unknown argument '$1' (try --help)" >&2; exit 3 ;;
  esac
done
for pair in "work_dir --work-dir" "coherence_file --coherence-file" "identity --identity" \
            "complete_out --complete-out" "partial_out --partial-out"; do
  set -- $pair
  [ -n "${!1}" ] || { echo "recheck-record.sh: $2 is required" >&2; exit 3; }
done
[ -f "$work_dir/comparator.verdicts" ] || { echo "recheck-record.sh: $work_dir/comparator.verdicts is missing" >&2; exit 3; }
[ -f "$work_dir/kernel.verdicts" ] || { echo "recheck-record.sh: $work_dir/kernel.verdicts is missing" >&2; exit 3; }
[ -f "$coherence_file" ] || { echo "recheck-record.sh: $coherence_file is missing" >&2; exit 3; }

lines_file="$(mktemp)"
trap 'rm -f "$lines_file"' EXIT

# One line per verdict, in the byte-stable form recheck.txt records (no wall times).
{
  awk '{ c = $1; v = $2; $1 = $2 = $3 = ""; sub(/^ +/, ""); print "comparator", c, v, $0 }' "$work_dir/comparator.verdicts"
  awk '{ k = $1; p = $2; v = $3; m = $4; d = $5; $1 = $2 = $3 = $4 = $5 = $6 = ""; sub(/^ +/, ""); print k, p, v, m, d, $0 }' "$work_dir/kernel.verdicts"
} > "$lines_file"

while IFS= read -r l; do
  case "$(echo "$l" | awk '{ print $3 }')" in
    FAIL) echo "[FAIL] $l" ;;
    NOT-RUN) echo "[skip] $l -- NOT RUN" ;;
    OK|EXPECTED-REJECTION) echo "[ok] $l" ;;
    *) echo "[FAIL] unrecognised verdict: $l"; verdict_fail=1 ;;
  esac
done < "$lines_file"

recheck_completeness="$(recheck_record_completeness "$lines_file")"
recheck_produced="$(recheck_produced_on)"
if [ "$recheck_completeness" = complete ]; then
  recheck_target="$complete_out"
else
  recheck_target="$partial_out"
fi
# Display paths relative to EX (framed_channel/), matching every other generated-file message in
# check.sh ("written to certificate/axioms.txt", never the absolute path); a target outside EX
# (a caller's own scratch directory, e.g. ci-macos-recheck.yml's $RUNNER_TEMP) is shown as given.
recheck_target_display="${recheck_target#"$EX"/}"
complete_out_display="${complete_out#"$EX"/}"

{
  echo "# framed_channel independent recheck (generated by check.sh --recheck; do not edit)"
  if [ "$recheck_completeness" != complete ]; then
    echo "# PARTIAL RECORD -- not the canonical certificate/recheck.txt: $recheck_completeness"
    echo "# A partial record is never adopted as certificate/recheck.txt; see certificate/README.md"
    echo "# and scripts/adopt-recheck.sh for the CI-produced, complete record."
  fi
  echo "# What each checker establishes, and what it does not: certificate/README.md, \"recheck.txt\","
  echo "# and every manifest's trust.G0_checker.independent_recheck block. This record is current only"
  echo "# while the identity below equals the identity line of digests.txt."
  echo "certificate identity: $identity"
  echo "produced on: $recheck_produced"
  echo "record: $recheck_completeness"
  echo
  echo "## tool revisions"
  recheck_tool_revisions
  echo
  echo "## revision coherence (recheck-revs.sh, at recheck time)"
  cat "$coherence_file"
  echo
  echo "## sandbox deviations"
  echo "# Grants recheck/landrun-shim.sh adds to Comparator's own landrun arguments, per room (<room> is"
  echo "# the fresh room's path, <toolchain> the elan Lean toolchain). Each is explained in"
  echo "# recheck/landrun-shim.sh; none grants write access outside the room's .lake directories."
  echo "# A 'PATH: lake is ...' line is not a grant: where the toolchain's lake is a shell wrapper,"
  echo "# the rooms run the binary it wraps (scripts/recheck-comparator.sh explains why)."
  if [ -s "$work_dir/comparator.deviations" ]; then
    awk '{ r = $1; $1 = ""; sub(/^ /, ""); rooms[$0] = rooms[$0] (rooms[$0] ? "," : "") r } END { for (g in rooms) print g "  [" rooms[g] "]" }' \
      "$work_dir/comparator.deviations" | LC_ALL=C sort
  else
    echo "(none recorded: Comparator did not run)"
  fi
  echo
  echo "## hardening (added restrictions, not deviations)"
  echo "# The static design (systemd-run --user without AF_UNIX, the outer landrun --best-effort"
  echo "# confinement, the bridge room's before/after package hash): certificate/README.md's"
  echo "# recheck.txt section, \"hardening\". This run's Landlock/network probes: revision coherence"
  echo "# above."
  echo
  echo "## Comparator's assumptions, and how each was met"
  if ! awk '$2 == "OK" || $2 == "EXPECTED-REJECTION" { f = 1 } END { exit !f }' "$work_dir/comparator.verdicts"; then
    echo "# Comparator produced no verdict in this run (see verdicts): the lines below state the design, not a run."
  fi
  echo "# 1, 2, 4, 6 (trusted imports, no prior compilation, landrun, privilege) do not vary run to"
  echo "# run: certificate/README.md's recheck.txt section, \"Comparator's six assumptions\"."
  echo "3. binaries: comparator, lean4export and the toolchain revisions above, checked by recheck-revs.sh"
  echo "5. kernel: Comparator's in-process Lean $COMPARATOR_KERNEL_VERSION kernel on a lean4export export of the $(tr -d '[:space:]' < "$EX/lean/lean-toolchain") build; no external_kernels (nanoda NOT CLAIMED)"
  echo
  echo "## verdicts"
  echo "# comparator <config> <OK|EXPECTED-REJECTION|FAIL|NOT-RUN> <outcome or reason>"
  echo "# <checker> <package> <OK|FAIL|NOT-RUN> modules=<m> declarations=<n|-> <scope or reason>"
  sed 's/^/verdict: /' "$lines_file"
} > "$recheck_target"

ok_n="$(awk '$3 == "OK" || $3 == "EXPECTED-REJECTION"' "$lines_file" | grep -c .)"
notrun_n="$(awk '$3 == "NOT-RUN"' "$lines_file" | grep -c .)"
if [ -n "${verdict_fail:-}" ] || awk '$3 == "FAIL" { f = 1 } END { exit !f }' "$lines_file"; then
  # check.sh's original FAIL message names the absolute path here (unlike the [ok] messages
  # below, which use the "certificate/recheck.txt"-relative form) -- preserved as-is.
  echo "recheck-record.sh: the independent recheck FAILED; see above and $recheck_target" >&2
  exit 1
fi
if [ "$recheck_completeness" = complete ]; then
  echo "[ok] independent recheck: $ok_n verdict(s) OK or EXPECTED-REJECTION, $notrun_n NOT RUN; written to $recheck_target_display"
  exit 0
fi
echo "[ok] independent recheck ran ($ok_n verdict(s) OK or EXPECTED-REJECTION, $notrun_n NOT RUN), but the record is PARTIAL ($recheck_completeness); written to $recheck_target_display, NOT $complete_out_display"
exit 2
