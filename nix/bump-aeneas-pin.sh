#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# bump-aeneas-pin.sh -- implements the "middle rule" (30-day cap) pin-selection and
# pin-move procedure for nix/aeneas-pin.json, in one scripted, idempotent, stateless run.
#
# Eligibility (checked per candidate before it can cost a gate): the asset digests match the
# release's own, the bundle's lean-toolchain equals ours, and the charon binary the bundle ships
# reports exactly the revision that candidate's own upstream `charon-pin` file names. A release
# whose bundled charon disagrees with its charon-pin is internally inconsistent (its Lean library
# and its extractor were built against different Charon revisions) and is never selectable; an
# unreadable charon-pin is treated the same way (fail closed). framed_channel's
# aeneas_rev_coherence re-checks the same equality at gate time against the fetched sources.
#
# Rule: pick the newest Aeneas nightly release with prebuilt
# assets for every supported system (x86_64-linux, aarch64-linux, aarch64-darwin) that passes the
# gate ("complete"). If the newest release with just the two Linux assets ("Linux-complete", `L`)
# that passes the gate is itself complete, select it. Otherwise, search complete eligible releases
# older than `L`, newest first, for one within --window-days (default 30, inclusive) of `L`'s
# commit date that passes the gate (`C`); select `C` if found. If not (window exhausted, or the
# --max-gates budget is spent first), select `L` and set macos_fallback: true.
#
# Usage: bash nix/bump-aeneas-pin.sh [--tag <tag>] [--max-gates N] [--window-days D]
#                                     [--check-only] [--dry-run] [--apply-ungated] [--now <iso>]
#   --tag <tag>       force this one release as the candidate; the automatic L/C rule is not run
#                      (reported as rule "n/a (--tag forced, reported but not applied)" in the
#                      summary). Still runs the eligibility/digest checks and, unless
#                      --check-only/--dry-run, the gate.
#   --max-gates N      bound the total number of real gates run across the whole search (default
#                      4). A candidate already at the current pin, or rejected on eligibility or
#                      digest before ever reaching the gate, does not consume this budget.
#   --window-days D    the middle-rule cap in days (default 30; documented policy is 30 -- this
#                      flag exists for fixtures only). Boundary is inclusive: exactly D days old
#                      is still "within" the window.
#   --check-only       run the selection with every real gate skipped (the first eligible
#                      candidate on each branch is treated as passing). Reports the L/C pair the
#                      rule would test, and the resulting selection. Writes nothing -- matches
#                      this repository's --dry-run convention elsewhere (full-gate.sh,
#                      adopt-recheck.sh): report the resolved action and its cost, write nothing.
#   --dry-run          a synonym for --check-only (same report-nothing-written behaviour). Kept
#                      as its own flag for readers who reach for --dry-run by habit.
#   --apply-ungated    run the same skipped-gate selection as --check-only, but then actually
#                      apply (write) the selected candidate's pin JSON, flake.lock override and
#                      lakefile.toml/lake-manifest.json -- without ever running the heavy gate
#                      (aeneas_rev_coherence / refresh-extraction.sh / refresh-candidates.sh /
#                      check.sh) to confirm it. This is what --dry-run used to mean here; renamed
#                      because writing files is the opposite of what --dry-run means everywhere
#                      else in this repository (see above).
#   --now <iso>        pin "the current time" for the --window-days arithmetic (fixtures only).
#
# With none of --check-only/--dry-run/--apply-ungated/--tag: runs the full algorithm for real.
# Each visited candidate (other than one already at the current pin, which auto-passes without
# spending a gate) is applied and gated in place; on gate failure the touched paths are restored
# exactly (nix/aeneas-pin.json, flake.lock,
# framed_channel/aeneas/{lakefile.toml,lake-manifest.json}, the Extracted/*.lean files,
# certificate/candidates.txt) and the search continues. Requires a clean working tree before
# starting (checked once, up front) so a restore is exact.
#
# The real gate is `check.sh --skip-approvals`: it checks every stage except approvals, because
# any candidate that moves charon_rev changes candidates.txt's `# charon:` header, which stales
# the recorded candidates_sha256 -- a deterministic, by-design approvals failure that is not a
# reason to reject an otherwise-good candidate. Re-approval (`approve.sh --review` / `--record`)
# is a human (or recorded-agent) step that runs after a candidate is selected, not part of the
# search. A candidate whose only remaining gap is a trusted-model edit (e.g. a hand-written
# externals file such as FunsExternal.lean, after an upstream rename) fails the gate's
# extraction-staleness check and cannot be auto-selected, by design -- the search never makes a
# trusted-model edit. Adopting such a candidate is a manual step; see docs/development.md's
# pin-bump procedure.
#
# If the selected candidate already equals the current pin (by full revision), prints "already
# current" and writes nothing, regardless of mode.
#
# Prints a machine-readable JSON summary (selected, branch, macos_fallback, reason, L, C,
# direction, distance_days, diff_stats, already_current, commit_date_fallback_used, gate_failures)
# to stdout as its last line, for a caller (a CI workflow's PR-body step) to consume with jq.
# `gate_failures` is a (possibly empty) array of {tag, stage}: every candidate that spent a real
# gate and failed it, in visit order, `stage` being the last diagnostic line of the captured gate
# output (a `[FAIL] ...` line, or one prefixed refresh-extraction.sh:/refresh-candidates.sh:/
# check.sh:), or "unknown"; under a test-hook gate (BUMP_PIN_TEST_GATE_JSON) `stage` is always
# "test-hook". A
# non-empty `gate_failures` on an otherwise-green run (including "already current") means a
# by-design failure was hit and worked around during the search, and is worth surfacing even
# though the run itself succeeded. `reason` is set only on the linux-complete/macos_fallback
# branch (null otherwise), to one of: "window-exhausted" (no in-window complete candidate found),
# "budget-truncated" (--max-gates was spent before the window was exhausted), or absent/null when
# a complete candidate (L or C) was selected outright.
#
# Test hooks (env vars; never set by a human or by the weekly workflow -- see
# framed_channel/tests/bump-pin/run.sh):
#   BUMP_PIN_TEST_RELEASES_JSON    file: a JSON array standing in for the GitHub releases list
#                                  (each: {tag_name, created_at, assets:[{name,digest,url}]}).
#   BUMP_PIN_TEST_COMMIT_DATES_JSON  file: JSON object short_sha -> {commit_date, full_sha}
#                                  (missing entries exercise the release created_at fallback).
#   BUMP_PIN_TEST_BUNDLE_JSON      file: JSON object tag -> {lean_toolchain, charon_rev,
#                                  charon_pin, rust_nightly, digest_ok,
#                                  assets:{system:{name,sha256}|null}, darwin_job_failed},
#                                  standing in for the download+extract step and for the read of
#                                  the candidate revision's own upstream `charon-pin` file.
#   BUMP_PIN_TEST_GATE_JSON        file: JSON object tag -> "pass" | "fail", standing in for the
#                                  real aeneas_rev_coherence/refresh-*/check.sh gate.
#   BUMP_PIN_TEST_PIN_FILE         path: use this file instead of nix/aeneas-pin.json (read AND
#                                  written).
#   BUMP_PIN_TEST_LEAN_TOOLCHAIN   string: use this instead of reading
#                                  framed_channel/lean/lean-toolchain.
#   BUMP_PIN_TEST_APPLY_LOG        file: when set, the real `nix flake lock`/`lake update` calls
#                                  are replaced by an appended log line (the pin JSON is still
#                                  really written).
#   BUMP_PIN_TEST_SKIP_GIT         "1": skip the clean-tree precondition and the git-checkout part
#                                  of restore-on-failure (the pin-file part of restore always runs).
#
# Requires: bash >= 4.4, jq; gh and nix (only when the corresponding test hook is unset).
# Exit: 0 on a clean run (including "already current" and every --check-only/--dry-run/
#       --apply-ungated report), 1 when no candidate could be selected (no Linux-complete
#       eligible candidate passes), 2 on a usage error.

if [ -z "${BASH_VERSION:-}" ]; then
  echo "bump-aeneas-pin.sh: run with bash >= 4.4 (bash nix/bump-aeneas-pin.sh)" >&2
  exit 2
fi
case "$BASH_VERSION" in
  [0-3].*|4.[0-3].*)
    echo "bump-aeneas-pin.sh: bash >= 4.4 is required (this is bash $BASH_VERSION)" >&2
    exit 2 ;;
esac

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PIN_FILE="${BUMP_PIN_TEST_PIN_FILE:-$ROOT/nix/aeneas-pin.json}"
LAKEFILE="$ROOT/framed_channel/aeneas/lakefile.toml"
LEAN_TOOLCHAIN_FILE="$ROOT/framed_channel/lean/lean-toolchain"
REPO="AeneasVerif/aeneas"

if ! command -v jq > /dev/null 2>&1; then
  echo "bump-aeneas-pin.sh: jq is required (run inside nix develop)" >&2
  exit 2
fi

usage() { awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "${BASH_SOURCE[0]}"; }

forced_tag=""
max_gates=4
window_days=30
check_only=false
apply_ungated=false
now_override=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --tag)
      [ "$#" -ge 2 ] || { echo "bump-aeneas-pin.sh: --tag needs a value" >&2; exit 2; }
      forced_tag="$2"; shift 2 ;;
    --max-gates)
      [ "$#" -ge 2 ] || { echo "bump-aeneas-pin.sh: --max-gates needs a value" >&2; exit 2; }
      max_gates="$2"; shift 2 ;;
    --window-days)
      [ "$#" -ge 2 ] || { echo "bump-aeneas-pin.sh: --window-days needs a value" >&2; exit 2; }
      window_days="$2"; shift 2 ;;
    # --dry-run is a synonym for --check-only (report-only, write nothing), matching this
    # repository's --dry-run convention elsewhere. --apply-ungated is the (renamed) old
    # "run the skipped-gate selection, then actually write" mode -- see the header comment.
    --check-only|--dry-run) check_only=true; shift ;;
    --apply-ungated) apply_ungated=true; shift ;;
    --now)
      [ "$#" -ge 2 ] || { echo "bump-aeneas-pin.sh: --now needs a value" >&2; exit 2; }
      now_override="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "bump-aeneas-pin.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done

case "$max_gates" in ''|*[!0-9]*)
  echo "bump-aeneas-pin.sh: --max-gates must be a non-negative integer" >&2; exit 2 ;;
esac
case "$window_days" in ''|*[!0-9]*)
  echo "bump-aeneas-pin.sh: --window-days must be a non-negative integer" >&2; exit 2 ;;
esac

# ------------------------------------------------------------------------------- date helpers
to_epoch() {
  local iso="$1"
  date -u -d "$iso" +%s 2>/dev/null || date -u -j -f "%Y-%m-%dT%H:%M:%SZ" "$iso" +%s 2>/dev/null
}

# --now is accepted for interface stability/fixture reproducibility, but the middle rule compares
# candidate-to-candidate commit dates (L's date vs C's date), never against "now" -- so parsing it
# above is the only use; nothing here consults it further.
# shellcheck disable=SC2034 # reserved for interface stability; see the comment above
now_iso="${now_override:-$(date -u +%Y-%m-%dT%H:%M:%SZ)}"
window_seconds=$(( window_days * 86400 ))

# ------------------------------------------------------------------------------- releases
fetch_releases_raw() {
  if [ -n "${BUMP_PIN_TEST_RELEASES_JSON:-}" ]; then
    cat "$BUMP_PIN_TEST_RELEASES_JSON"
  else
    gh api "repos/$REPO/releases" --paginate --jq '.[]' | jq -s '.'
  fi
}

local_lean_toolchain="${BUMP_PIN_TEST_LEAN_TOOLCHAIN:-}"
if [ -z "$local_lean_toolchain" ]; then
  local_lean_toolchain="$(tr -d '[:space:]' < "$LEAN_TOOLCHAIN_FILE" 2>/dev/null || true)"
fi

FALLBACK_TAGS=()

# candidates_json: every nightly-* release, deduplicated by short sha (keeping the first, i.e.
# newest, occurrence -- collapses a re-tag of the same commit), classified linux_complete/complete.
raw="$(fetch_releases_raw)"
candidates_json="$(jq '
  [ .[] | select(.tag_name | test("^nightly-")) | {
      tag: .tag_name,
      short_sha: (.tag_name | split("-") | last),
      created_at: .created_at,
      assets: [ .assets[]? | {name, digest: (.digest // ""), url: .browser_download_url} ]
    } ]
  | reduce .[] as $r ([]; if any(.[]; .short_sha == $r.short_sha) then . else . + [$r] end)
  | [ .[] | . + {
      has_x86: ([ .assets[] | select(.name == "aeneas-linux-x86_64.tar.gz") ] | length > 0),
      has_aarch64_linux: ([ .assets[] | select(.name == "aeneas-linux-aarch64.tar.gz") ] | length > 0),
      has_darwin: ([ .assets[] | select(.name == "aeneas-macos-aarch64.tar.gz") ] | length > 0)
    } ]
  | [ .[] | . + {linux_complete: (.has_x86 and .has_aarch64_linux)} ]
  | [ .[] | . + {complete: (.linux_complete and .has_darwin)} ]
' <<< "$raw")"

# ------------------------------------------------------------------------------- commit info
declare -A COMMIT_FULLSHA COMMIT_DATE
commit_info_for() {
  local short="$1" created_at="$2"
  [ -n "${COMMIT_DATE[$short]:-}" ] && return 0
  if [ -n "${BUMP_PIN_TEST_COMMIT_DATES_JSON:-}" ]; then
    local d full
    d="$(jq -r --arg s "$short" '.[$s].commit_date // empty' "$BUMP_PIN_TEST_COMMIT_DATES_JSON")"
    full="$(jq -r --arg s "$short" '.[$s].full_sha // empty' "$BUMP_PIN_TEST_COMMIT_DATES_JSON")"
    if [ -n "$d" ]; then
      COMMIT_DATE[$short]="$d"; COMMIT_FULLSHA[$short]="${full:-$short}"
    else
      COMMIT_DATE[$short]="$created_at"; COMMIT_FULLSHA[$short]="$short"
      FALLBACK_TAGS+=("$short")
    fi
    return 0
  fi
  local resp sha date
  if resp="$(gh api "repos/$REPO/commits/$short" 2>/dev/null)" \
      && sha="$(jq -r '.sha // empty' <<< "$resp")" \
      && date="$(jq -r '.commit.committer.date // empty' <<< "$resp")" \
      && [ -n "$sha" ] && [ -n "$date" ]; then
    COMMIT_FULLSHA[$short]="$sha"; COMMIT_DATE[$short]="$date"
  else
    COMMIT_FULLSHA[$short]="$short"; COMMIT_DATE[$short]="$created_at"
    FALLBACK_TAGS+=("$short")
  fi
}

# Resolve commit info for every Linux-complete-or-complete candidate up front (needed to sort by
# real commit date, per the plan: "release age is the tagged commit's committer date, not the
# tag's date string").
mapfile -t relevant_shorts < <(jq -r '[.[] | select(.linux_complete or .complete) | .short_sha] | unique[]' <<< "$candidates_json")
for short in "${relevant_shorts[@]}"; do
  created_at="$(jq -r --arg s "$short" '[.[] | select(.short_sha == $s)][0].created_at' <<< "$candidates_json")"
  commit_info_for "$short" "$created_at"
done

# candidates_dated_json: linux_complete/complete candidates with resolved commit_date/full_sha,
# sorted newest commit_date first (this is the re-sort the plan requires -- GitHub's own listing
# order is by publish/created_at, not by the tagged commit's real date).
commit_map_json="$(
  { for short in "${relevant_shorts[@]}"; do
      jq -n --arg s "$short" --arg d "${COMMIT_DATE[$short]}" --arg f "${COMMIT_FULLSHA[$short]}" \
        '{($s): {commit_date: $d, full_sha: $f}}'
    done
  } | jq -s 'add // {}'
)"
candidates_dated_json="$(jq --argjson m "$commit_map_json" '
  [ .[] | select(.linux_complete or .complete) | . + {
      commit_date: ($m[.short_sha].commit_date // .created_at),
      full_sha: ($m[.short_sha].full_sha // .short_sha)
    } ]
  | sort_by(.commit_date) | reverse
' <<< "$candidates_json")"

linux_complete_list_json="$(jq '[.[] | select(.linux_complete)]' <<< "$candidates_dated_json")"
complete_list_json="$(jq '[.[] | select(.complete)]' <<< "$candidates_dated_json")"

# ------------------------------------------------------------------------------- bundle read
declare -A BUNDLE_JSON
darwin_job_failed_for() {
  # Best-effort only: this script does not auto-query Aeneas's own Actions API for a per-tag
  # darwin-job failure (fragile without knowing their exact workflow/job naming). It always
  # reports false here; a maintainer sets source_build_known_broken by hand after investigating a
  # specific failure, and the pin file's existing entry for a still-asset-less system is preserved
  # (see the caller below), never overwritten to false.
  echo false
}

ensure_bundle() {
  local tag="$1" cand_json="$2" full_sha="${3:-}"
  [ -n "${BUNDLE_JSON[$tag]:-}" ] && return 0
  if [ -n "${BUMP_PIN_TEST_BUNDLE_JSON:-}" ]; then
    BUNDLE_JSON[$tag]="$(jq --arg t "$tag" '.[$t]' "$BUMP_PIN_TEST_BUNDLE_JSON")"
    if [ "${BUNDLE_JSON[$tag]}" = "null" ]; then
      BUNDLE_JSON[$tag]='{"lean_toolchain":"","charon_rev":"","charon_pin":"","rust_nightly":"","digest_ok":false,"assets":{},"darwin_job_failed":false}'
    fi
    return 0
  fi
  local -A names=( [x86_64-linux]="aeneas-linux-x86_64.tar.gz" [aarch64-linux]="aeneas-linux-aarch64.tar.gz" [aarch64-darwin]="aeneas-macos-aarch64.tar.gz" )
  local assets_json='{}' ok=true lean="" rust="" charon=""
  local sys
  for sys in x86_64-linux aarch64-linux aarch64-darwin; do
    local name="${names[$sys]}" url digest
    url="$(jq -r --arg n "$name" '[.assets[] | select(.name == $n)][0].url // empty' <<< "$cand_json")"
    if [ -z "$url" ]; then
      assets_json="$(jq --arg s "$sys" '. + {($s): null}' <<< "$assets_json")"
      continue
    fi
    digest="$(jq -r --arg n "$name" '[.assets[] | select(.name == $n)][0].digest // empty' <<< "$cand_json")"
    local pjson sri
    if ! pjson="$(nix store prefetch-file --json "$url" 2>/dev/null)"; then
      ok=false
      continue
    fi
    sri="$(jq -r '.hash' <<< "$pjson")"
    if [ -n "$digest" ]; then
      local want hex_got
      want="${digest#sha256:}"
      hex_got="$(nix hash convert --hash-algo sha256 --to base16 "$sri" 2>/dev/null | sed 's/^sha256://')"
      [ "$hex_got" = "$want" ] || ok=false
    fi
    assets_json="$(jq --arg s "$sys" --arg n "$name" --arg h "$sri" '. + {($s): {name: $n, sha256: $h}}' <<< "$assets_json")"
    if [ "$sys" = x86_64-linux ]; then
      local store_path work
      store_path="$(jq -r '.storePath' <<< "$pjson")"
      work="$(mktemp -d)"
      tar -xzf "$store_path" -C "$work" 2>/dev/null || true
      # The release tarball has NO top-level wrapper directory (confirmed by extracting a real
      # asset: aeneas, charon, charon-driver, rust-toolchain and backends/ all land directly in
      # the extraction root) -- unlike a typical GitHub source archive. nix/aeneas-prebuilt.nix's
      # own unpackPhase relies on this same fact.
      rust="$(grep -h 'channel' "$work/rust-toolchain" 2>/dev/null | sed -n 's/.*"nightly-\([0-9-]*\)".*/\1/p' | head -1)"
      lean="$(cat "$work/backends/lean/lean-toolchain" 2>/dev/null | tr -d '[:space:]')"
      charon="$( (cd "$work" && ./charon version 2>/dev/null) | sed -n 's/.*(\([0-9a-f]*\)).*/\1/p')"
      rm -rf "$work"
    fi
  done
  # The candidate revision's own charon-pin: first line that is neither blank nor a comment,
  # exactly as framed_channel/scripts/lib/aeneas-revs.sh reads the fetched copy. Empty when the
  # file cannot be read, which visit_candidate treats as ineligible.
  local charon_pin=""
  if [ -n "$full_sha" ]; then
    charon_pin="$(gh api -H "Accept: application/vnd.github.raw" \
        "repos/$REPO/contents/charon-pin?ref=$full_sha" 2>/dev/null |
      grep -vE '^[[:space:]]*(#|$)' | head -1 | tr -d '[:space:]')"
  fi
  local db
  db="$(darwin_job_failed_for "$tag")"
  BUNDLE_JSON[$tag]="$(jq -n --argjson assets "$assets_json" --arg lean "$lean" --arg rust "$rust" \
    --arg charon "$charon" --arg charon_pin "$charon_pin" --argjson ok "$ok" --argjson db "$db" \
    '{lean_toolchain:$lean, rust_nightly:$rust, charon_rev:$charon, charon_pin:$charon_pin, digest_ok:$ok, assets:$assets, darwin_job_failed:$db}')"
}

# ------------------------------------------------------------------------------- current pin
current_rev="" current_commit_date=""
if [ -f "$PIN_FILE" ]; then
  current_rev="$(jq -r '.rev // empty' "$PIN_FILE" 2>/dev/null)"
  current_commit_date="$(jq -r '.commit_date // empty' "$PIN_FILE" 2>/dev/null)"
fi
ORIG_PIN_CONTENT=""
[ -f "$PIN_FILE" ] && ORIG_PIN_CONTENT="$(cat "$PIN_FILE")"

# ------------------------------------------------------------------------------- apply/gate
restore_touched() {
  if [ -n "$ORIG_PIN_CONTENT" ]; then
    # ORIG_PIN_CONTENT was captured via "$(cat "$PIN_FILE")", and command substitution
    # strips ALL trailing newlines -- so a bare `printf '%s'` here would write the pin file
    # back one trailing newline short of what git has committed. Since every writer of this
    # file (apply_candidate's `jq -n ... > "$PIN_FILE"`, and the file as checked into git)
    # always ends with exactly one trailing newline, `printf '%s\n'` restores the original
    # byte-for-byte. Without this, `git diff --quiet -- nix/aeneas-pin.json` (the workflow's
    # own `changed` detection) sees a spurious one-byte diff after ANY failed real-gate
    # attempt, even when the ultimately selected candidate is already current -- see
    # run-ledger.md's root-cause triage for the first observed instance of this on a live
    # runner (update-aeneas-pin.yml run 35538836978).
    printf '%s\n' "$ORIG_PIN_CONTENT" > "$PIN_FILE"
  fi
  if [ -z "${BUMP_PIN_TEST_SKIP_GIT:-}" ]; then
    ( cd "$ROOT" && git checkout -- \
        flake.lock \
        framed_channel/aeneas/lakefile.toml \
        framed_channel/aeneas/lake-manifest.json \
        framed_channel/aeneas/FramedChannelAeneas/Extracted/Types.lean \
        framed_channel/aeneas/FramedChannelAeneas/Extracted/Funs.lean \
        framed_channel/certificate/candidates.txt 2>/dev/null || true )
  fi
}

apply_candidate() {
  local tag="$1" full_sha="$2" commit_date="$3" is_complete="$4"
  local bundle="${BUNDLE_JSON[$tag]}"
  local known_broken='{}'
  if [ "$is_complete" != true ]; then
    # Preserve any previously-recorded known-broken entry for a still-asset-less darwin; the
    # script never auto-sets it (see darwin_job_failed_for's own comment), only clears it.
    known_broken="$(jq -c '.source_build_known_broken // {}' <<< "$ORIG_PIN_CONTENT" 2>/dev/null || echo '{}')"
  fi
  local macos_fallback
  if [ "$is_complete" = true ]; then macos_fallback=false; else macos_fallback=true; fi
  jq -n \
    --arg tag "$tag" --arg rev "$full_sha" --arg cd "$commit_date" \
    --arg charon "$(jq -r '.charon_rev' <<< "$bundle")" \
    --arg rustn "$(jq -r '.rust_nightly' <<< "$bundle")" \
    --arg lean "$(jq -r '.lean_toolchain' <<< "$bundle")" \
    --argjson assets "$(jq '.assets' <<< "$bundle")" \
    --argjson comps '["rustc-dev","llvm-tools","rust-src","miri"]' \
    --argjson known_broken "$known_broken" \
    --argjson macos_fallback "$macos_fallback" \
    '{tag:$tag, rev:$rev, commit_date:$cd, charon_rev:$charon, rust_nightly:$rustn,
      rust_components:$comps, lean_toolchain:$lean, assets:$assets,
      source_build_known_broken:$known_broken, macos_fallback:$macos_fallback}' > "$PIN_FILE"
  if [ -n "${BUMP_PIN_TEST_APPLY_LOG:-}" ]; then
    {
      echo "apply: nix flake lock --override-input aeneas github:AeneasVerif/aeneas/$full_sha"
      echo "apply: lakefile.toml rev=$full_sha"
      echo "apply: lake update --keep-toolchain aeneas"
    } >> "$BUMP_PIN_TEST_APPLY_LOG"
  else
    ( cd "$ROOT" && nix flake lock --override-input aeneas "github:AeneasVerif/aeneas/$full_sha" )
    sed -i "s/^rev = \".*\"/rev = \"$full_sha\"/" "$LAKEFILE"
    ( cd "$ROOT/framed_channel/aeneas" && lake update --keep-toolchain aeneas )
  fi
}

# DIFF_STATS: set only by a real (non-test-hook) successful gate, to the `git diff --stat` of the
# extraction/candidates files it just regenerated. It is overwritten by each subsequent
# successful real gate, so by the time the algorithm finishes it always reflects the truly
# selected candidate's own diff (a failed, restored candidate never touches it) -- see the
# apply_and_gate/restore_touched contract just below.
DIFF_STATS=""
# gate_stage_of: reads a failed gate's captured output on stdin and prints the diagnostic line
# naming what failed, or "unknown". The LAST matching line, never the first: the gate runs under
# `set -e`, so the failing command is the last one to print, while every earlier command that
# succeeded has already printed a line with the same prefix (refresh-extraction.sh's "rewrote
# Types.lean and Funs.lean ..." would otherwise be blamed for every later check.sh failure).
# `[FAIL]` is how aeneas_rev_coherence and most check.sh stages report.
gate_stage_of() {
  local line
  line="$(grep -E '^(\[FAIL\] |(refresh-extraction\.sh|refresh-candidates\.sh|check\.sh): )' | tail -n 1)"
  printf '%s\n' "${line:-unknown}"
}
# LAST_GATE_STAGE: set by run_gate_real on a real-gate failure only, to gate_stage_of's reading of
# the captured output (see gate_failures_json below). Read once, immediately, by gate_pass.
LAST_GATE_STAGE=""
run_gate_real() {
  local out
  LAST_GATE_STAGE=""
  # --skip-approvals: this is the search gate only, never the verification claim. Any candidate
  # that moves charon_rev changes candidates.txt's `# charon:` header, which stales the recorded
  # candidates_sha256 -- a deterministic approvals failure unrelated to whether the candidate is
  # otherwise good. Re-approval happens after selection (see docs/development.md); see
  # check.sh --help for --skip-approvals' own contract (internal-only, never combined with
  # --recheck/--recheck-fresh/--require-person-approval).
  if ! out="$(cd "$ROOT" && nix develop .#extraction --command bash -lc '
      set -e
      # shellcheck source=framed_channel/scripts/lib/aeneas-revs.sh
      . framed_channel/scripts/lib/aeneas-revs.sh
      aeneas_rev_coherence
      bash framed_channel/scripts/refresh-extraction.sh
      bash framed_channel/scripts/refresh-candidates.sh
      bash framed_channel/check.sh --skip-approvals
    ' 2>&1)"; then
    echo "$out" >&2
    LAST_GATE_STAGE="$(printf '%s\n' "$out" | gate_stage_of)"
    return 1
  fi
  if [ -z "${BUMP_PIN_TEST_SKIP_GIT:-}" ]; then
    DIFF_STATS="$(cd "$ROOT" && git diff --stat -- \
      framed_channel/aeneas/FramedChannelAeneas/Extracted framed_channel/certificate/candidates.txt 2>/dev/null)"
  fi
  return 0
}

# GATE_FAILURES: every {tag, stage} a real gate (or the test-hook gate) recorded a failure for,
# in visit order. Read by gate_failures_json (below) into the summary JSON's gate_failures field.
GATE_FAILURES=()
record_gate_failure() {
  local tag="$1" stage="$2"
  GATE_FAILURES+=("$(jq -n --arg tag "$tag" --arg stage "$stage" '{tag:$tag, stage:$stage}')")
}
gate_failures_json() {
  if [ "${#GATE_FAILURES[@]}" -eq 0 ]; then
    echo '[]'
  else
    printf '%s\n' "${GATE_FAILURES[@]}" | jq -s '.'
  fi
}

GATES_USED=0
gate_pass() {
  local tag="$1"
  if [ -n "${BUMP_PIN_TEST_GATE_JSON:-}" ]; then
    local v
    v="$(jq -r --arg t "$tag" '.[$t] // "fail"' "$BUMP_PIN_TEST_GATE_JSON")"
    if [ "$v" = "pass" ]; then
      return 0
    fi
    record_gate_failure "$tag" "test-hook"
    return 1
  fi
  if run_gate_real; then
    return 0
  fi
  record_gate_failure "$tag" "$LAST_GATE_STAGE"
  return 1
}

# apply_and_gate TAG FULL_SHA COMMIT_DATE IS_COMPLETE -> 0 pass, 1 fail (restored)
apply_and_gate() {
  local tag="$1" full_sha="$2" commit_date="$3" is_complete="$4"
  apply_candidate "$tag" "$full_sha" "$commit_date" "$is_complete"
  if gate_pass "$tag"; then
    return 0
  else
    restore_touched
    return 1
  fi
}

# ------------------------------------------------------------------------------- clean-tree gate
if ! $check_only && ! $apply_ungated && [ -z "${BUMP_PIN_TEST_SKIP_GIT:-}" ]; then
  if [ -n "$(cd "$ROOT" && git status --porcelain 2>/dev/null)" ]; then
    echo "bump-aeneas-pin.sh: working tree is not clean; commit or stash before running a real bump" >&2
    exit 1
  fi
fi

# ------------------------------------------------------------------------------- eligibility
# visit_candidate TAG CAND_JSON -> sets VISIT (pass|already_current|ineligible|digest|fail), never
# consumes budget for already_current/ineligible/digest.
VISIT=""
visit_candidate() {
  local tag="$1" cand_json="$2" complete_flag="$3"
  local short full_sha commit_date
  short="$(jq -r '.short_sha' <<< "$cand_json")"
  full_sha="${COMMIT_FULLSHA[$short]}"
  commit_date="${COMMIT_DATE[$short]}"
  if [ -n "$current_rev" ] && [ "$full_sha" = "$current_rev" ]; then
    VISIT=already_current
    return 0
  fi
  ensure_bundle "$tag" "$cand_json" "$full_sha"
  local bundle="${BUNDLE_JSON[$tag]}"
  if [ "$(jq -r '.digest_ok' <<< "$bundle")" != true ]; then
    echo "note: candidate $tag rejected: asset digest mismatch" >&2
    VISIT=digest
    return 0
  fi
  local bundle_lean
  bundle_lean="$(jq -r '.lean_toolchain' <<< "$bundle")"
  if [ -n "$local_lean_toolchain" ] && [ "$bundle_lean" != "$local_lean_toolchain" ]; then
    echo "Lean bump available at $tag: manual task" >&2
    VISIT=ineligible
    return 0
  fi
  local bundle_charon upstream_charon_pin
  bundle_charon="$(jq -r '.charon_rev // ""' <<< "$bundle")"
  upstream_charon_pin="$(jq -r '.charon_pin // ""' <<< "$bundle")"
  if [ -z "$upstream_charon_pin" ]; then
    echo "note: candidate $tag rejected: its upstream charon-pin could not be read, so the bundled charon cannot be checked against it" >&2
    VISIT=ineligible
    return 0
  fi
  if [ "$bundle_charon" != "$upstream_charon_pin" ]; then
    echo "note: candidate $tag rejected: bundled charon is '$bundle_charon', but its own charon-pin is $upstream_charon_pin" >&2
    VISIT=ineligible
    return 0
  fi
  if $check_only || $apply_ungated; then
    VISIT=pass
    return 0
  fi
  if [ "$GATES_USED" -ge "$max_gates" ]; then
    VISIT=budget
    return 0
  fi
  GATES_USED=$((GATES_USED + 1))
  if apply_and_gate "$tag" "$full_sha" "$commit_date" "$complete_flag"; then
    VISIT=pass
  else
    echo "note: candidate $tag failed the gate" >&2
    VISIT=fail
  fi
}

# ------------------------------------------------------------------------------- forced --tag
# "The rule is then reported but not applied" (plan wording): --tag is a report-only investigation
# aid. It runs the eligibility/digest checks for exactly this one release (never the automatic L/C
# search) and never gates for real or writes anything -- regardless of --check-only/--dry-run/
# --apply-ungated.
if [ -n "$forced_tag" ]; then
  cand_json="$(jq --arg t "$forced_tag" '[.[] | select(.tag == $t)][0] // empty' <<< "$candidates_json")"
  if [ -z "$cand_json" ] || [ "$cand_json" = null ]; then
    echo "bump-aeneas-pin.sh: --tag $forced_tag not found among nightly-* releases" >&2
    exit 1
  fi
  short="$(jq -r '.short_sha' <<< "$cand_json")"
  created_at="$(jq -r '.created_at' <<< "$cand_json")"
  commit_info_for "$short" "$created_at"
  complete_flag="$(jq -r '.complete' <<< "$cand_json")"
  check_only=true # force the gate-skip path in visit_candidate; --tag never applies or gates
  visit_candidate "$forced_tag" "$cand_json" "$complete_flag"
  full_sha="${COMMIT_FULLSHA[$short]}"
  commit_date="${COMMIT_DATE[$short]}"
  case "$VISIT" in
    already_current)
      jq -n --arg tag "$forced_tag" --arg rev "$full_sha" \
        '{already_current:true, selected:{tag:$tag, rev:$rev}, rule:"n/a (--tag forced, reported but not applied)", gate_failures:[]}'
      exit 0 ;;
    pass)
      distance_days=0
      direction="none"
      if [ -n "$current_commit_date" ]; then
        cd_e="$(to_epoch "$commit_date")"; cur_e="$(to_epoch "$current_commit_date")"
        if [ "$cd_e" -gt "$cur_e" ]; then direction=forward; distance_days=$(( (cd_e - cur_e) / 86400 ))
        elif [ "$cd_e" -lt "$cur_e" ]; then direction=backward; distance_days=$(( (cur_e - cd_e) / 86400 ))
        fi
      fi
      jq -n --arg tag "$forced_tag" --arg rev "$full_sha" --arg cd "$commit_date" \
        --argjson complete "$complete_flag" --arg dir "$direction" --argjson dist "$distance_days" \
        '{already_current:false, selected:{tag:$tag, rev:$rev, commit_date:$cd, complete:$complete},
          rule:"n/a (--tag forced, reported but not applied)", direction:$dir, distance_days:$dist, gate_failures:[]}'
      exit 0 ;;
    *)
      echo "bump-aeneas-pin.sh: --tag $forced_tag is not eligible ($VISIT)" >&2
      exit 1 ;;
  esac
fi

# ------------------------------------------------------------------------------- walk: find L
L_json="" L_full="" L_date=""
budget_hit_on_L=false
mapfile -t lc_rows < <(jq -c '.[]' <<< "$linux_complete_list_json")
for row in "${lc_rows[@]}"; do
  tag="$(jq -r '.tag' <<< "$row")"
  visit_candidate "$tag" "$row" "$(jq -r '.complete' <<< "$row")"
  case "$VISIT" in
    already_current|pass)
      L_json="$row"
      short="$(jq -r '.short_sha' <<< "$row")"
      L_full="${COMMIT_FULLSHA[$short]}"
      L_date="${COMMIT_DATE[$short]}"
      break ;;
    budget) budget_hit_on_L=true; break ;;
    *) continue ;;
  esac
done

if [ -z "$L_json" ]; then
  if $budget_hit_on_L; then
    echo "bump-aeneas-pin.sh: no Linux-complete eligible candidate passed the gate within --max-gates ($max_gates)" >&2
  else
    echo "bump-aeneas-pin.sh: no Linux-complete eligible candidate passed the gate" >&2
  fi
  jq -n --argjson gf "$(gate_failures_json)" '{selected:null, branch:null, reason:"no-linux-complete-candidate", gate_failures:$gf}'
  exit 1
fi

# ------------------------------------------------------------------------------- L complete?
selected_json="" selected_full="" selected_date="" branch="" reason="" macos_fallback=false
C_json="" C_full="" C_date=""

if [ "$(jq -r '.complete' <<< "$L_json")" = true ]; then
  selected_json="$L_json"; selected_full="$L_full"; selected_date="$L_date"
  branch="complete"; macos_fallback=false
else
  L_epoch="$(to_epoch "$L_date")"
  budget_hit_on_C=false
  mapfile -t c_rows < <(jq -c --arg lt "$(jq -r '.tag' <<< "$L_json")" \
      '[.[] | select(.tag != $lt)] | .[]' <<< "$complete_list_json")
  for row in "${c_rows[@]}"; do
    tag="$(jq -r '.tag' <<< "$row")"
    short="$(jq -r '.short_sha' <<< "$row")"
    commit_info_for "$short" "$(jq -r '.created_at' <<< "$row")"
    c_epoch="$(to_epoch "${COMMIT_DATE[$short]}")"
    if [ "$c_epoch" -ge "$L_epoch" ]; then
      continue # not older than L
    fi
    if [ $(( L_epoch - c_epoch )) -gt "$window_seconds" ]; then
      break # older candidates are further still, so no in-window complete candidate remains
    fi
    visit_candidate "$tag" "$row" true
    case "$VISIT" in
      already_current|pass)
        C_json="$row"; C_full="${COMMIT_FULLSHA[$short]}"; C_date="${COMMIT_DATE[$short]}"
        break ;;
      budget) budget_hit_on_C=true; break ;;
      *) continue ;;
    esac
  done
  if [ -n "$C_json" ]; then
    selected_json="$C_json"; selected_full="$C_full"; selected_date="$C_date"
    branch="complete"; macos_fallback=false
  else
    selected_json="$L_json"; selected_full="$L_full"; selected_date="$L_date"
    branch="linux-complete"; macos_fallback=true
    if $budget_hit_on_C; then reason="budget-truncated"; else reason="window-exhausted"; fi
  fi
fi

selected_tag="$(jq -r '.tag' <<< "$selected_json")"
selected_complete="$(jq -r '.complete' <<< "$selected_json")"

# ------------------------------------------------------------------------------- already current?
if [ -n "$current_rev" ] && [ "$selected_full" = "$current_rev" ]; then
  jq -n --arg tag "$selected_tag" --arg rev "$selected_full" --arg branch "$branch" \
    --argjson gf "$(gate_failures_json)" \
    '{already_current:true, selected:{tag:$tag, rev:$rev}, branch:$branch, gate_failures:$gf}'
  echo "bump-aeneas-pin.sh: already current ($selected_tag)" >&2
  exit 0
fi

direction="none"; distance_days=0
if [ -n "$current_commit_date" ]; then
  sel_e="$(to_epoch "$selected_date")"; cur_e="$(to_epoch "$current_commit_date")"
  if [ -n "$sel_e" ] && [ -n "$cur_e" ]; then
    if [ "$sel_e" -gt "$cur_e" ]; then direction=forward; distance_days=$(( (sel_e - cur_e) / 86400 ))
    elif [ "$sel_e" -lt "$cur_e" ]; then direction=backward; distance_days=$(( (cur_e - sel_e) / 86400 ))
    fi
  fi
fi

L_summary="$(jq -n --arg tag "$(jq -r '.tag' <<< "$L_json")" --arg rev "$L_full" --arg cd "$L_date" '{tag:$tag, rev:$rev, commit_date:$cd}')"
C_summary="null"
[ -n "$C_json" ] && C_summary="$(jq -n --arg tag "$(jq -r '.tag' <<< "$C_json")" --arg rev "$C_full" --arg cd "$C_date" '{tag:$tag, rev:$rev, commit_date:$cd}')"

fallback_tags_json="$(printf '%s\n' "${FALLBACK_TAGS[@]-}" | jq -R 'select(length>0)' | jq -s '.')"

summary() {
  jq -n \
    --arg tag "$selected_tag" --arg rev "$selected_full" --arg cd "$selected_date" \
    --argjson complete "$selected_complete" --arg branch "$branch" --argjson mf "$macos_fallback" \
    --arg reason "$reason" --argjson L "$L_summary" --argjson C "$C_summary" \
    --arg dir "$direction" --argjson dist "$distance_days" --argjson fb "$fallback_tags_json" \
    --arg diffstats "$DIFF_STATS" --argjson already_current false \
    --argjson gf "$(gate_failures_json)" \
    '{selected:{tag:$tag, rev:$rev, commit_date:$cd, complete:$complete}, branch:$branch,
      macos_fallback:$mf, reason:$reason, L:$L, C:$C, direction:$dir, distance_days:$dist,
      commit_date_fallback_used:$fb, diff_stats:(if ($diffstats|length)>0 then $diffstats else null end),
      already_current:$already_current, gate_failures:$gf}'
}

if $check_only; then
  summary
  exit 0
fi

# --------------------------------------------------------------------------- apply the winner
# By this point selected_full != current_rev is guaranteed (the exact-match case already exited
# above). Unconditionally (re)apply the winner's files:
#   - --check-only/--dry-run already returned above; never reached here.
#   - --apply-ungated never applied anything during the walk (visit_candidate short-circuits to
#     "pass" without gating), so this is the one and only write -- "applies the selected
#     candidate without the gate".
#   - a real run already applied+gated the winner once as the last candidate visited in the walk
#     (unless a losing candidate for the OTHER branch was tried afterward and restored -- e.g. `L`
#     passed, then a `C` candidate was tried and failed and was restored to the ORIGINAL pin, not
#     to `L`'s state). Reapplying here is therefore not just idempotent bookkeeping: it is what
#     guarantees the tree ends on `selected`, never on whatever the last restore left behind. It
#     costs one extra (deterministic, idempotent) `nix flake lock`/`lake update` when the winner
#     was already the last thing applied; it never reruns the heavy gate.
apply_candidate "$selected_tag" "$selected_full" "$selected_date" "$selected_complete"

summary
echo "bump-aeneas-pin.sh: selected $selected_tag ($branch${macos_fallback:+, macos_fallback})" >&2
