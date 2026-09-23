#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# check.sh -- the verification gate for the framed_channel worked example.
#
# Runs the stages in order and stops at the first red one. The approvals stage runs last, so a run
# whose only failure is there means "not yet (re-)approved". Stages and flags: bash check.sh --help.
# What each stage checks and which certificate files it writes: README.md and certificate/README.md.
#
# The gate includes the aeneas/ bridge package (the extraction and its bridge proofs): a plain run
# builds and audits it, and fails before building anything when charon or aeneas is off PATH.
# --core-only is the fast offline development pre-check: it leaves the bridge out, ends INCOMPLETE
# (exit 3), writes nothing under certificate/, and is not the verification claim.
# --committed-extraction builds and audits BOTH packages against the committed extraction as-is,
# without charon or aeneas (only jq is required): the extraction/candidate staleness check is
# skipped (NOT CHECKED), it also ends INCOMPLETE (exit 3) and writes nothing under certificate/,
# and it is not the verification claim either. Use full-gate.sh for the gate itself.
#
# Requires: bash >= 4.4, coreutils (sha256sum), awk, perl, the Lean toolchain pinned in
# lean/lean-toolchain; cargo, rustfmt and clippy unless --lean-only; charon, aeneas and jq (the
# repository's nix develop shell) plus network and about 7 GB on the first fetch of the bridge's
# dependencies (Aeneas + Mathlib), unless --core-only or --committed-extraction (jq alone still
# required).
# Exit: 0 pass, 1 a stage failed, 2 usage error or missing prerequisite, 3 core-only or
# committed-extraction pre-check complete (INCOMPLETE; not the verification claim).

# Before any bash-4 syntax is parsed, so an old bash (or sh) gets a clear message.
if [ -z "${BASH_VERSION:-}" ]; then
  echo "check.sh: run with bash >= 4.4 (bash check.sh)" >&2
  exit 2
fi
case "$BASH_VERSION" in
  [0-3].*|4.[0-3].*)
    echo "check.sh: bash >= 4.4 is required (this is bash $BASH_VERSION)" >&2
    exit 2 ;;
esac

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CERT="$EX/certificate"
AXIOMS="$CERT/axioms.txt"
DIGESTS="$CERT/digests.txt"
LADDER="$CERT/ladder.txt"
COUNTERMODELS="$CERT/countermodels.txt"
RECHECK="$CERT/recheck.txt"
# A recheck run whose record is not complete (some verdict other than the optional
# lean4lean-fresh line is NOT-RUN -- e.g. Comparator on a non-Linux host) is never written to
# RECHECK; it goes here instead, and RECHECK is left untouched. Gitignored: never the canonical
# record. See certificate-identity.sh's "record: complete" check and certificate/README.md.
RECHECK_PARTIAL="$CERT/recheck.partial.txt"
# shellcheck source=scripts/lib/packages.sh
. "$EX/scripts/lib/packages.sh"

# The hand-written axiom and shared-proof policy (policy_rows FILE KIND, from packages.sh).
POLICY="$CERT/policy.txt"
if [ ! -f "$POLICY" ]; then
  echo "check.sh: certificate/policy.txt is missing; it states the trusted axioms and the flagged allow-list" >&2
  exit 1
fi
if awk 'NF && $1 !~ /^#/ && $1 != "trusted" && $1 != "flagged" && $1 != "shared-proof" { bad = 1; print "check.sh: unknown row in certificate/policy.txt: " $0 > "/dev/stderr" } END { exit bad }' "$POLICY"; then :; else
  exit 1
fi

# The trusted axiom set (`trusted` rows). Nothing outside it may appear in any record.
mapfile -t TRUSTED < <(policy_rows "$POLICY" trusted)
if [ ${#TRUSTED[@]} -eq 0 ]; then
  echo "check.sh: certificate/policy.txt has no trusted rows" >&2
  exit 1
fi

# Compiler-trusting axioms, permitted only for the `flagged` rows. `bv_decide` records a
# per-declaration helper axiom `<decl>._native.bv_decide.ax_<n>_<m>` instead (is_compiler_trusting).
COMPILER_TRUSTING=(Lean.ofReduceBool Lean.trustCompiler)
mapfile -t FLAGGED < <(policy_rows "$POLICY" flagged)

# Bank aggregates splice every row's proof into one definition, so their records carry the flagged
# row's axioms by construction; they are excused for compiler-trusting axioms only, and only while
# FLAGGED is non-empty. Audited only for a package that ran.
CORE_AGGREGATES=(FramedChannel.items FramedChannel.bank)
BRIDGE_AGGREGATES=(FramedChannel.Bridge.allItems FramedChannel.Bridge.allBank)

# >>> layer-rules -- tests/layer/run.sh extracts this block verbatim, between these two markers,
# so the self-test exercises the gate's own regexes and its own matcher rather than a copy. Keep
# the markers, and keep everything between them free of state the stage has not set up yet.
#
# The queue models, derived rather than typed, so no component name appears in a layer rule: the
# unit names under lean/FramedChannel/Model/ whose proof module declares a `BoundedQueueLaws`
# instance, read from the `Model/<X>/Theorems.lean` spelling the layout rule fixes.
queue_model_units=()
while IFS= read -r qm_file; do
  [ -n "$qm_file" ] || continue
  grep -qE '^[[:space:]]*instance[[:space:]].*:[[:space:]]*BoundedQueueLaws[[:space:]]' "$qm_file" || continue
  qm_rel="${qm_file#"$EX"/lean/FramedChannel/Model/}"
  case "$qm_rel" in
    */Theorems.lean) queue_model_units+=("${qm_rel%/Theorems.lean}") ;;
    *)               continue ;;
  esac
done <<< "$(find "$EX/lean/FramedChannel/Model" -name '*.lean' -not -path '*/.lake/*' | LC_ALL=C sort)"
if [ ${#queue_model_units[@]} -eq 0 ]; then
  echo "check.sh: no queue model found under lean/FramedChannel/Model (no unit whose proof module declares a BoundedQueueLaws instance), so the composition layer rule below would forbid nothing" >&2
  exit 1
fi
QUEUE_MODELS_RE="$( IFS='|'; printf '%s' "${queue_model_units[*]}" )"

# The layer import rule: "<files, as an extended regex over paths relative to EX>;<forbidden
# import, as an extended regex over the module name>;<why>". The composition layer is proved from
# the laws alone, so its generic module may not see a queue model; models may not see
# compositions; specifications may see neither; and the core package never sees Aeneas.
#
# The first rule names `<Unit>/Defs.lean` and `<Unit>/Theorems.lean` and deliberately NOT
# `<Unit>/Instances.lean`: instantiating the generic composition AT a queue model is exactly that
# module's job, so it is the one composition module that must be allowed to import one. The
# exclusion is the rule's content, not a gap in it (tests/layer/run.sh asserts both halves).
LAYER_RULES=(
  "^lean/FramedChannel/Composition/[A-Za-z0-9]+/(Defs|Theorems)\.lean\$;^FramedChannel\.Model\.(${QUEUE_MODELS_RE})(\..*)?\$;the generic channel is proved from the queue laws, not from a queue model"
  "^lean/FramedChannel/Model/;^FramedChannel\.Composition\.;a model may not depend on a composition"
  "^lean/FramedChannel/Spec/;^FramedChannel\.(Model|Composition)\.;a specification may not depend on a model or a composition"
  "^lean/;^(Aeneas|Mathlib)($|\.);the core package stays free of Aeneas and Mathlib"
  "^(lean/FramedChannel|aeneas/FramedChannelAeneas)/|^aeneas/GenVectors\.lean$;^FramedChannel(Aeneas)?Challenge($|\.);no proof module, registry or generator imports the statement-only specification"
  "^(lean|aeneas)/;^FramedChannel\.Evidence($|\.);countermodels are evidence, not dependencies: nothing imports an Evidence module"
  "^lean/FramedChannel/Spec/;^FramedChannel\.Ladder$;a specification states obligations; the proof-ladder tooling belongs to proof modules"
)

# The allow-only layer rules: "<files regex>;<the ONLY imports allowed, as a regex over the module
# name>;<why>". The definitions layer and the statement-only Challenge libraries are what an
# approval covers and what Comparator trusts as imports, so what they may see is listed, not excluded.
DEFS_MODULE_RE='FramedChannel\.Spec\.[A-Za-z0-9]+|FramedChannel\.(Model|Composition)\.[A-Za-z0-9]+\.Defs|FramedChannelAeneas\.Bridge\.[A-Za-z0-9]+\.Defs'
LAYER_ALLOW_RULES=(
  "^lean/FramedChannel/(Model|Composition)/[A-Za-z0-9]+/Defs\.lean$|^aeneas/FramedChannelAeneas/Bridge/[A-Za-z0-9]+/Defs\.lean$;^(${DEFS_MODULE_RE}|FramedChannelAeneas\.Extracted\.[A-Za-z0-9]+|Std\.Tactic\.BVDecide)$;a definitions module may import only specification, definitions and extraction modules, never a proof module"
  "^lean/FramedChannelChallenge(/[A-Za-z0-9]+)?\.lean$|^aeneas/FramedChannelAeneasChallenge(/[A-Za-z0-9]+)?\.lean$;^(${DEFS_MODULE_RE}|FramedChannelAeneas\.Extracted\.[A-Za-z0-9]+|Aeneas|FramedChannel(Aeneas)?Challenge(\.[A-Za-z0-9]+)?)$;a Challenge module may import only specification, definitions, extraction, Aeneas and Challenge modules"
)

# layer_violations REL [IMPORT...]: one line per rule the module at REL breaks, empty when it
# breaks none. The layer-import stage below and tests/layer/run.sh both call this, so the
# self-test cannot drift from what the gate actually applies.
layer_violations() {
  local rel="$1"; shift
  local rule file_re import_re allow_re why imp
  for rule in "${LAYER_RULES[@]}"; do
    IFS=';' read -r file_re import_re why <<< "$rule"
    [[ "$rel" =~ $file_re ]] || continue
    for imp in "$@"; do
      if [[ "$imp" =~ $import_re ]]; then
        echo "$rel imports $imp: $why"
      fi
    done
  done
  for rule in "${LAYER_ALLOW_RULES[@]}"; do
    IFS=';' read -r file_re allow_re why <<< "$rule"
    [[ "$rel" =~ $file_re ]] || continue
    for imp in "$@"; do
      if ! [[ "$imp" =~ $allow_re ]]; then
        echo "$rel imports $imp: $why"
      fi
    done
  done
}
# <<< layer-rules

# A vacuous definition is semantically sorry: a body that is trivially true, carrying no content
# from the obligation it claims to discharge.
VACUOUS_RE='^[[:space:]]*(noncomputable[[:space:]]+)?(def|theorem|lemma|instance)[^:]*:=[[:space:]]*(True|Unit|trivial|Trivial)[[:space:]]*$'

# A search tactic: `exact?`, `apply?`, `try?`, `grind?` or a `+suggestions` configuration.
SEARCH_TACTIC_RE='exact\?|apply\?|try\?|grind\?|\+suggestions'

# A source line that emits a proof-ladder record (see lean/FramedChannel/Ladder.lean).
LADDER_SRC_RE='^[[:space:]]*(rung[[:space:]]|ladder_record%|refuted%)'

usage() {
  cat <<'EOF'
check.sh -- the verification gate for the framed_channel worked example.

Usage:
  bash check.sh               the verification gate: build, audit, format-check, lint and test
                              both packages, the aeneas/ bridge included (charon, aeneas and jq
                              on PATH; the bridge's dependencies, Aeneas + Mathlib, are fetched
                              if absent: about 7 GB, network, once)
  bash check.sh --core-only   the fast offline development pre-check: the extraction staleness
                              and bridge stages are skipped and every check that depends on them
                              is reported NOT CHECKED or UNAUDITED; ends INCOMPLETE with exit 3,
                              never PASS; writes nothing under certificate/; is not the
                              verification claim
  bash check.sh --committed-extraction
                              build and audit BOTH packages against the committed extraction as
                              it stands, without charon or aeneas (only jq is required): the
                              extraction/candidate staleness check alone is skipped, reported NOT
                              CHECKED; every other stage runs; ends INCOMPLETE with exit 3, never
                              PASS; writes nothing under certificate/; is not the verification
                              claim; mutually exclusive with --core-only, and refused with
                              --recheck/--recheck-fresh (a recheck record is always over both
                              packages against a checked extraction). See full-gate.sh for the
                              gate itself.
  bash check.sh --aeneas      accepted as the explicit spelling of the default (the bridge is
                              part of the gate, never optional)
  bash check.sh --clean       remove the core package's lean/.lake build cache first (the
                              bridge's aeneas/.lake and recheck/.lake are kept)
  bash check.sh --lean-only   skip cargo fmt/clippy/test (for a machine with no Rust toolchain)
  bash check.sh --recheck     also run the independent recheck: a Lean4Lean + leanchecker replay
                              of every module of both packages runs on any platform, and Comparator
                              in fresh clean rooms runs additionally on Linux (about 7 minutes,
                              plus a one-time build of recheck/, which needs network; refused with
                              --core-only, since a recheck record is always over both packages).
                              Comparator is reported NOT-RUN, reason "Landlock sandbox is
                              Linux-only", on any other platform. A run with every verdict
                              accounted for (no NOT-RUN outside the optional lean4lean-fresh line)
                              writes certificate/recheck.txt; any other run (e.g. Comparator
                              NOT-RUN on macOS) writes the same content instead to the gitignored
                              certificate/recheck.partial.txt and never touches recheck.txt -- a
                              partial record can never be mistaken for the canonical one. CI
                              produces a complete record on Linux and uploads it as an artifact;
                              see framed_channel/scripts/adopt-recheck.sh to adopt one locally.
                              Exit status is 0 whether the record is complete or PARTIAL (a
                              PARTIAL record is the only possible local result on a non-Linux
                              host, since Comparator is Linux-only); verify.yml's own recheck
                              producer job is what escalates a PARTIAL record to a CI failure,
                              because that job specifically is the record's producer, for which
                              PARTIAL is a real failure rather than an expected local limitation.
                              With RECHECK_DIAG_DIR=<dir> set, every log of the recheck (each
                              Comparator room's full output and landrun-shim log, the bridge
                              pre-flight's stderr, the kernel replay's per-module logs, both
                              scripts' own output) is copied to <dir> whatever the outcome; the
                              record itself keeps only each failure's last line. CI sets it and
                              uploads the directory when the job fails.
  bash check.sh --recheck-fresh
                              --recheck, plus Lean4Lean over the core registry's whole import
                              closure (Init, Std, Lean; about 5 more minutes)
  bash check.sh --require-person-approval
                              fail an approval recorded by an agent (by default the approvals
                              stage accepts records by a person or by an agent)
  bash check.sh --skip-approvals
                              internal to nix/bump-aeneas-pin.sh's search gate only: run every
                              stage except approvals, which prints SKIPPED and is not attempted;
                              exit 0 when every other stage passes. Never the verification claim.
                              Refused with --recheck/--recheck-fresh/--require-person-approval
                              (exit 2), since those act on the approvals stage this skips.
  bash check.sh -h, --help    this text

Stages, in order: certificate identity (computed), aeneas revision coherence, extraction
staleness, layer import rule, license headers, core package, bridge package, registry statement
hashes, specification consistency, selection consistency, differential vectors, axiom audit,
proof ladder, manifest cross-check, independent recheck (run only with --recheck; otherwise the
stored record is reported current or STALE), cargo fmt --check, cargo clippy, cargo test,
certificate identity (unchanged during the run), approvals.

Requires bash >= 4.4, coreutils, awk, perl, the Lean toolchain pinned in lean/lean-toolchain
(elan installs it on demand) and, unless --lean-only, cargo with rustfmt and clippy. The gate
also requires charon, aeneas and jq, and fetches the bridge's dependencies when they are absent
(about 7 GB, network, the first time); a missing tool fails the run (exit 2) before anything is
built. From the repository root, `bash full-gate.sh` resolves the fastest available route for
your system and runs the gate (see `full-gate.sh --help`); or, when your system's pin has a
prebuilt asset, `nix develop .#extraction --command bash framed_channel/check.sh` directly.
Without those tools, or offline, `--core-only` is the pre-check: it skips the extraction
staleness and bridge stages with a note and ends INCOMPLETE, which is not the claim.
`--committed-extraction` (only jq required) instead builds and audits both packages against the
committed extraction as-is, skipping only the extraction/candidate staleness check; it also ends
INCOMPLETE, and is also not the claim.

Exit status: 0 pass (covers both a complete and a PARTIAL --recheck record locally; see
--recheck above), 1 a stage failed, 2 usage error or missing prerequisite, 3 core-only or
committed-extraction pre-check complete (INCOMPLETE; not the verification claim).
EOF
}

clean=false
lean_only=false
# precheck_mode: full (the verification claim), core_only or committed_extraction (both end
# INCOMPLETE; see usage above). precheck_flag renders the current non-full mode's own flag
# spelling ("--core-only"/"--committed-extraction"), for the sites below that interpolate it into
# an otherwise mode-specific message; it is never called while precheck_mode=full.
precheck_mode=full
precheck_flag() {
  case "$precheck_mode" in
    core_only) echo "--core-only" ;;
    committed_extraction) echo "--committed-extraction" ;;
  esac
}
# core_only_seen/committed_extraction_seen: only for the mutual-exclusion checks below, which
# preserve their original fixed priority order (core-only+recheck, then
# committed-extraction+core-only, then committed-extraction+recheck) regardless of argument order
# -- precheck_mode alone cannot tell "both flags were given" from "the second one was given" once
# a later flag has overwritten it.
core_only_seen=false
committed_extraction_seen=false
recheck=false
recheck_fresh=false
require_person=false
# skip_approvals: internal to nix/bump-aeneas-pin.sh's search gate only (run_gate_real). It skips
# the approvals stage entirely (not even NOT CHECKED -- SKIPPED) so that a candidate whose only
# difference is a new charon_rev, which stales the recorded candidates_sha256, can still be
# selected. A run with --skip-approvals is never the verification claim; see the approvals-stage
# branch below and full-gate.sh/check.sh --help, which both mark it internal-only.
skip_approvals=false
for arg in "$@"; do
  case "$arg" in
    --recheck) recheck=true ;;
    --recheck-fresh) recheck=true; recheck_fresh=true ;;
    --clean) clean=true ;;
    --lean-only) lean_only=true ;;
    --core-only) precheck_mode=core_only; core_only_seen=true ;;
    --committed-extraction) precheck_mode=committed_extraction; committed_extraction_seen=true ;;
    # The bridge is part of the gate, so --aeneas is the explicit spelling of the default.
    --aeneas) ;;
    --no-aeneas)
      echo "check.sh: --no-aeneas is not a mode: the bridge package is part of the verification gate." >&2
      echo "  --core-only is the fast offline pre-check (it ends INCOMPLETE, exit 3, and is not the claim)." >&2
      exit 2 ;;
    --require-person-approval) require_person=true ;;
    --skip-approvals) skip_approvals=true ;;
    -h|--help) usage; exit 0 ;;
    *) echo "check.sh: unknown argument '$arg' (try --help)" >&2; exit 2 ;;
  esac
done
if $core_only_seen && $recheck; then
  echo "check.sh: --core-only cannot be combined with --recheck or --recheck-fresh: a recheck record is" >&2
  echo "  always over both packages, and a core-only run writes nothing under certificate/." >&2
  exit 2
fi
if $committed_extraction_seen && $core_only_seen; then
  echo "check.sh: --committed-extraction cannot be combined with --core-only: --core-only leaves the" >&2
  echo "  bridge package out entirely, while --committed-extraction builds and audits it." >&2
  exit 2
fi
if $committed_extraction_seen && $recheck; then
  echo "check.sh: --committed-extraction cannot be combined with --recheck or --recheck-fresh: a recheck" >&2
  echo "  record is always over both packages against a checked extraction, and a committed-extraction" >&2
  echo "  run writes nothing under certificate/ and never checks the extraction against charon/aeneas." >&2
  exit 2
fi
if $skip_approvals && { $recheck || $require_person; }; then
  echo "check.sh: --skip-approvals cannot be combined with --recheck, --recheck-fresh or" >&2
  echo "  --require-person-approval: it skips the approvals stage entirely, so there is nothing for" >&2
  echo "  those flags to act on. --skip-approvals is internal to nix/bump-aeneas-pin.sh's search gate" >&2
  echo "  and is never the verification claim; see --help." >&2
  exit 2
fi

in_list() {
  local needle="$1"; shift
  local x
  for x in "$@"; do
    [ "$x" = "$needle" ] && return 0
  done
  return 1
}

# fail_each (scripts/lib/packages.sh) is used below.

# is_compiler_trusting AXIOM: true for a COMPILER_TRUSTING name, or for a native `bv_decide`
# helper axiom belonging to a FLAGGED declaration. The record names the helper relative to the
# namespace it is printed from (`crc8_step_linear._native...` on the declaration itself,
# `Crc8.crc8_step_linear._native...` on an aggregate), so the match is on the suffix after the
# flagged declaration's last name component. A helper axiom of any OTHER declaration is not
# compiler-trusting in this sense: it falls through to "outside the trusted set".
is_compiler_trusting() {
  local ax="$1" f short
  in_list "$ax" "${COMPILER_TRUSTING[@]}" && return 0
  for f in "${FLAGGED[@]}"; do
    short="${f##*.}"
    if [[ "$ax" =~ (^|\.)${short}\._native\.bv_decide\.ax_[0-9]+_[0-9]+$ ]]; then
      return 0
    fi
  done
  return 1
}

mkdir -p "$CERT"

# ------------------------------------------------------------------------------------- preflight

# The gate needs charon, aeneas and jq for the extraction staleness stage, which cannot fetch
# them, so their absence is a missing prerequisite (exit 2), found before anything is built. The
# bridge's Lake dependencies are different: the bridge stage's own lake build fetches them, so
# their absence is announced (the cost is real) and the run proceeds.
# --committed-extraction trusts the committed extraction as-is and never invokes charon or aeneas,
# so it needs neither on PATH; it still needs jq (aeneas-revs.sh's pin-vs-lock check, among others).
if [ "$precheck_mode" != core_only ]; then
  for tool in charon aeneas jq; do
    if [ "$precheck_mode" = committed_extraction ] && { [ "$tool" = charon ] || [ "$tool" = aeneas ]; }; then
      continue
    fi
    if ! command -v "$tool" > /dev/null 2>&1; then
      echo "check.sh: $tool is not on PATH, and the verification gate needs it (extraction staleness stage)." >&2
      echo "  From the repository root: bash full-gate.sh (or nix develop .#extraction --command bash framed_channel/check.sh, when your system's pin has a prebuilt asset)" >&2
      echo "  For the fast offline pre-check without the bridge (INCOMPLETE, exit 3): bash check.sh --core-only" >&2
      if [ "$precheck_mode" = committed_extraction ]; then
        echo "  For the light in-shell audit without charon/aeneas (INCOMPLETE, exit 3): bash check.sh --committed-extraction (still needs jq)" >&2
      fi
      exit 2
    fi
  done
  if ! bridge_deps_fetched; then
    echo "note: the bridge package's dependencies (Aeneas, Mathlib) are not fetched; the bridge stage's"
    echo "      lake build fetches them (about 7 GB, network). --core-only is the offline pre-check."
  fi
fi

# lake itself, before anything is built. elan's `lake` is a proxy that execs the toolchain's real
# binary; nixpkgs' elan patches each toolchain it installs so its ELF interpreter and `cc` wrapper
# are /nix/store paths of the nixpkgs revision that installed it. After a nixpkgs relock plus a
# garbage collection (or a ~/.elan restored from another revision's cache) those paths are gone and
# every lake call dies with an opaque "No such file or directory (os error 2)". Name it here.
lake_toolchain="$(tr -d '[:space:]' < "$EX/lean/lean-toolchain")"
if ! command -v lake > /dev/null 2>&1; then
  echo "check.sh: lake is not on PATH; run inside nix develop (from the repository root)" >&2
  exit 2
fi
if ! lake_probe="$(cd "$EX/lean" && lake --version 2>&1)"; then
  echo "check.sh: lake is on PATH but cannot run ('lake --version' in lean/ failed):" >&2
  printf '%s\n' "$lake_probe" | sed 's/^/    /' >&2
  echo "  Likely cause: the installed toolchain $lake_toolchain under ${ELAN_HOME:-$HOME/.elan}/toolchains" >&2
  echo "  was set up by a different nixpkgs revision, and its binaries reference /nix/store paths" >&2
  echo "  that no longer exist (a nixpkgs relock followed by a garbage collection, or a ~/.elan" >&2
  echo "  restored from an older cache). 'No such file or directory (os error 2)' is this symptom." >&2
  echo "  Remedy: elan toolchain uninstall $lake_toolchain   (then re-enter the dev shell and re-run;" >&2
  echo "  elan reinstalls it against the current nixpkgs). A network failure while elan downloads a" >&2
  echo "  missing toolchain looks different: the output above names the download." >&2
  exit 2
fi

# The certificate identity of the inputs this run checks (see certificate-identity.sh). Computed
# before anything is built, so every generated file can name it; recomputed before the approvals.
# shellcheck source=scripts/certificate-identity.sh
. "$EX/scripts/certificate-identity.sh"
if ! IDENTITY_LINES="$(identity_digest_lines "$EX")"; then
  echo "check.sh: could not digest the certificate inputs (a listed file is missing)" >&2
  exit 1
fi
IDENTITY="sha256:$(printf '%s\n' "$IDENTITY_LINES" | identity_of_lines)"
echo "certificate identity: $IDENTITY"

# Every temporary file lives under one directory, removed once on exit however the run ends.
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# A core-only or committed-extraction run is not the verification claim, so neither ever writes
# under certificate/: its four generated files go under the run's own temporary directory and
# vanish with it. RECHECK stays at the committed file, which either mode only reads (for the
# current/STALE report; --recheck is refused with both above), so certificate-identity.sh --check
# can never find a core-only or committed-extraction file naming the identity a full run would name.
if [ "$precheck_mode" != full ]; then
  precheck_dir="$(precheck_flag)"; precheck_dir="${precheck_dir#--}"
  mkdir -p "$work/$precheck_dir"
  AXIOMS="$work/$precheck_dir/axioms.txt"
  DIGESTS="$work/$precheck_dir/digests.txt"
  LADDER="$work/$precheck_dir/ladder.txt"
  COUNTERMODELS="$work/$precheck_dir/countermodels.txt"
fi

# ------------------------------------------------------------------------------ aeneas revisions

echo "== aeneas revision coherence =="
# shellcheck source=scripts/lib/aeneas-revs.sh
. "$EX/scripts/lib/aeneas-revs.sh"
# A committed-extraction run never invokes charon or aeneas (the preflight above does not even
# require them), so binaries of those names that happen to be on PATH are not its inputs.
coherence_mode=""
[ "$precheck_mode" = committed_extraction ] && coherence_mode="--no-binaries"
if ! aeneas_rev_coherence $coherence_mode; then
  echo "check.sh: the extraction's pinned revisions disagree; see above"
  exit 1
fi

# --------------------------------------------------------------------- comparator pin coherence

# Build-free (no Comparator on PATH, no `lake build`): a partial Comparator pin bump fails here,
# in the default (non---recheck) path, without needing Comparator built. See
# scripts/lib/recheck-revs.sh's recheck_pin_coherence header comment.
echo "== comparator pin coherence =="
if [ -z "${_RECHECK_REVS_SOURCED:-}" ]; then
  # shellcheck source=scripts/lib/recheck-revs.sh
  . "$EX/scripts/lib/recheck-revs.sh"
fi
if ! recheck_pin_coherence; then
  echo "check.sh: nix/comparator-pin.json disagrees with recheck/lakefile.toml or recheck/lake-manifest.json; see above"
  exit 1
fi

# -------------------------------------------------------------------------- extraction staleness

# Regenerate the extraction and the candidate set into a temporary directory and diff; never
# rewrite them (refresh-extraction.sh and refresh-candidates.sh do). FunsExternal.lean is
# hand-written: the --dest run polices its `rust_fun` names and the bridge package stage scans it.
staleness_ran=false
echo "== extraction staleness =="
if [ "$precheck_mode" = core_only ]; then
  echo "[skip] extraction and candidate staleness (--core-only)"
elif [ "$precheck_mode" = committed_extraction ]; then
  echo "[skip] extraction and candidate staleness (--committed-extraction: the committed extraction is trusted as-is, NOT CHECKED)"
elif ! command -v charon > /dev/null 2>&1 || ! command -v aeneas > /dev/null 2>&1; then
  # The preflight already required both; this is a defence against PATH changing, not a mode.
  echo "[FAIL] charon/aeneas are not on PATH; the gate needs them (run via full-gate.sh or nix develop .#extraction, or use --core-only/--committed-extraction for a pre-check)"
  exit 2
else
  extract_dir="$work/extraction"
  extract_log="$work/extraction.log"
  mkdir -p "$extract_dir"
  if ! bash "$EX/scripts/refresh-extraction.sh" --no-coherence --dest "$extract_dir" \
       --llbc-out "$work/crate.llbc" > "$extract_log" 2>&1; then
    echo "[FAIL] refresh-extraction.sh could not regenerate the extraction"
    cat "$extract_log"
    exit 1
  fi
  stale=false
  : > "$extract_log"
  for f in Types.lean Funs.lean; do
    if ! diff "$EX/aeneas/FramedChannelAeneas/Extracted/$f" "$extract_dir/$f" >> "$extract_log" 2>&1; then
      stale=true
    fi
  done
  if $stale; then
    echo "[FAIL] aeneas/FramedChannelAeneas/Extracted/ is stale against rust/src"
    sed -n '1,40p' "$extract_log"
    echo "  Re-read the diff, then regenerate with:"
    echo "    bash scripts/refresh-extraction.sh"
    exit 1
  fi
  echo "[ok] extraction staleness (the committed extraction is what charon/aeneas produce now)"
  # The Select candidates of the same LLBC. refresh-candidates.sh --check writes nothing.
  if ! bash "$EX/scripts/refresh-candidates.sh" --check --llbc "$work/crate.llbc" > "$work/candidates.log" 2>&1; then
    echo "[FAIL] certificate/candidates.txt is stale against rust/src (or could not be regenerated)"
    sed -n '1,40p' "$work/candidates.log"
    echo "  Re-read the diff, then regenerate with:"
    echo "    bash scripts/refresh-candidates.sh"
    exit 1
  fi
  echo "[ok] candidate staleness (certificate/candidates.txt is what the same charon LLBC classifies)"
  staleness_ran=true
fi

# ----------------------------------------------------------------------------- layer import rule

echo "== layer import rule =="
layer_failures=0
layer_files=0
layer_imports=0
while IFS= read -r rel; do
  layer_files=$((layer_files + 1))
  imports="$(lean_imports "$EX/$rel")"
  # A parser that silently reads no imports would pass every rule.
  if [ -z "$imports" ] && grep -qE '^import[[:space:]]' "$EX/$rel"; then
    echo "[FAIL] $rel has import lines, but none were read from its header"
    layer_failures=$((layer_failures + 1))
  fi
  while IFS= read -r violation; do
    [ -n "$violation" ] || continue
    echo "[FAIL] $violation"
    layer_failures=$((layer_failures + 1))
  done <<< "$(layer_violations "$rel" $imports)"
  layer_imports=$((layer_imports + $(printf '%s' "$imports" | grep -c .)))
done <<< "$(cd "$EX" && find lean aeneas/FramedChannelAeneas aeneas/FramedChannelAeneasChallenge aeneas/FramedChannelAeneasChallenge.lean aeneas/GenVectors.lean -name '*.lean' -not -path '*/.lake/*' | LC_ALL=C sort)"
if [ $layer_failures -ne 0 ]; then
  echo "check.sh: $layer_failures layer import violation(s)"
  exit 1
fi
echo "[ok] layer import rule ($layer_files modules, $layer_imports imports, ${#LAYER_RULES[@]} exclusion rules, ${#LAYER_ALLOW_RULES[@]} allow-only rules; queue models derived: ${queue_model_units[*]})"

# ------------------------------------------------------------------------------- license headers

echo "== license headers =="
if ! spdx_out="$(bash "$EX/scripts/check-spdx.sh" 2>&1)"; then
  echo "$spdx_out"
  echo "check.sh: license header check failed"
  exit 1
fi
echo "$spdx_out"

# -------------------------------------------------------------------- the per-package Lean stage

# join_records LOG: print every `#print axioms` record in a Lake build log on one line. Lean wraps
# a long axiom list over several lines; Lake prefixes the first with `info: <module>:<l>:<c>: `.
join_records() {
  awk '
    /depends on axioms|does not depend on any axioms/ {
      line = $0
      while (line !~ /\]$/ && line !~ /does not depend/) {
        if ((getline nxt) <= 0) break
        gsub(/^[ \t]+/, "", nxt); line = line " " nxt
      }
      print line
    }' "$1"
}

# lean_package_stage NAME DIR ROOT GENERATED [EXTRA...]
#   NAME       package label (core, bridge)
#   DIR        the Lake package directory, relative to EX
#   ROOT       the library root directory inside DIR
#   GENERATED  space-separated paths (relative to DIR) of generated files, which the
#              vacuous-definition scan skips (they are policed by the extraction-staleness stage)
#   EXTRA      further hand-written Lean files, relative to DIR, that are scanned but not built
#              as part of the library
#
# Builds the package, falling back once to a cold build when Lake replays no log for a module
# that carries `#print axioms`; asserts that the audited module count equals the number of such
# files (discovery is recursive, so a module in any subdirectory counts); fails on a `sorry`, a
# bare `native_decide` or a vacuous definition; and writes this package's own records to
# $work/records.NAME and its module list to $work/modules.NAME.
lean_package_stage() {
  local name="$1" dir="$2" root="$3" generated="$4"
  shift 4
  local extras=("$@")
  local pkg="$EX/$dir" log="$work/build.$name.log" t0 t1 secs m missing audited expected_count

  local modules ladder_modules
  modules="$(cd "$pkg" && grep -rlE --include='*.lean' '^[[:space:]]*#print axioms ' "$root" | LC_ALL=C sort)"
  printf '%s\n' "$modules" | sed '/^$/d' > "$work/modules.$name"
  # Modules that emit proof-ladder records (`rung`, `ladder_record%`, `refuted%`). Their records
  # arrive through the same replayed build log as the axiom records, so a module whose log Lake
  # did not replay would silently drop them too: they join the missing-record check below.
  ladder_modules="$(cd "$pkg" && grep -rlE --include='*.lean' "$LADDER_SRC_RE" "$root" | LC_ALL=C sort)"

  run_package_build() {
    t0="$(date +%s)"
    ( cd "$pkg" && lake build ) > "$log" 2>&1
    local rc=$?
    t1="$(date +%s)"
    secs=$((t1 - t0))
    return $rc
  }
  missing_records() {
    for m in $(printf '%s\n' $modules $ladder_modules | LC_ALL=C sort -u); do
      grep -q "^info: $m:" "$log" || echo "$m"
    done
  }
  build_failed() {
    echo "[FAIL] lake build in $dir/ (${secs}s)"
    grep -vE '^(✔|⣿|trace)' "$log" | grep -vE '^info: .*depends on axioms' | tail -60
    exit 1
  }

  if ! run_package_build; then build_failed; fi
  missing="$(missing_records)"
  if [ -n "$missing" ]; then
    # Lake replays cached module logs, but NOT reliably for every already-built module, so an
    # incremental run can omit a module's records -- and a gate that audits only some of what it
    # built is not a gate. Only the package's own build products are removed, never its fetched
    # dependencies.
    echo "     incomplete audit capture in $dir/ (no replayed log for: $(echo "$missing" | tr '\n' ' '))"
    echo "     rebuilding $dir/ from scratch so the audit covers every module"
    rm -rf "$pkg/.lake/build"
    if ! run_package_build; then build_failed; fi
    missing="$(missing_records)"
    if [ -n "$missing" ]; then
      echo "[FAIL] no axiom records captured in $dir/ for: $(echo "$missing" | tr '\n' ' ')"
      exit 1
    fi
  fi

  expected_count="$(grep -c . "$work/modules.$name")"
  audited="$(for m in $modules; do grep -q "^info: $m:" "$log" && echo "$m"; done | grep -c .)"
  if [ "$audited" -ne "$expected_count" ]; then
    echo "[FAIL] $dir/: audited $audited module(s), but $expected_count .lean file(s) carry #print axioms"
    exit 1
  fi

  # Only this package's own records: a dependent package's log also replays its dependencies'.
  join_records "$log" | grep "^info: $root/" > "$work/records.$name"
  # The proof-ladder records (`ladder <decl> <method> [qualifier]`, `countermodel <cand> <witness>`),
  # with the module prefix stripped; the proof ladder stage judges them.
  grep -E "^info: $root/[^:]*:[0-9]+:[0-9]+: (ladder|countermodel) " "$log" |
    sed -E 's|^info: [^:]*:[0-9]+:[0-9]+: ||' > "$work/ladder.$name" || true

  # `sorry` is checked against the BUILD LOG, not by grepping the sources. Lean emits
  # "declaration uses `sorry`" for every declaration that contains one, so the log is exact; a
  # source grep would instead trip over every docstring that discusses sorry.
  local scan=0 ex_args=() g f
  if grep -nE "$LEAN_SORRY_MSG" "$log"; then
    echo "[FAIL] a declaration built in $dir/ uses 'sorry'"
    scan=1
  fi
  # `native_decide` is prohibited outright. Occurrences inside backticks are prose naming the
  # prohibition; a bare occurrence is a use. The axiom audit is the real gate (native_decide leaves
  # a compiler-trusting axiom), this scan names the source line.
  if ( cd "$pkg" && grep -rn --include='*.lean' 'native_decide' "$root" "${extras[@]}" ) | grep -v '`native_decide`'; then
    echo "[FAIL] bare 'native_decide' in a $dir/ Lean source"
    scan=1
  fi
  # Search tactics are discovery tools: a committed proof must carry what they found, never the
  # search, or the build would depend on a search result. Same convention as native_decide:
  # occurrences inside backticks are prose and are removed before matching. The ladder's own
  # module is exempt: its audit runs `exact?` as the canonical retrieval attempt, inside a saved
  # state that is always restored, so no proof term ever comes from it.
  if ( cd "$pkg" && grep -rnE --include='*.lean' "$SEARCH_TACTIC_RE" "$root" "${extras[@]}" ) |
       grep -v "^$root/Ladder\.lean:" | sed 's/`[^`]*`//g' | grep -E "$SEARCH_TACTIC_RE"; then
    echo "[FAIL] a search tactic (exact?, apply?, try?, grind?, +suggestions) in a $dir/ Lean source"
    scan=1
  fi
  # A `rung` must be the whole proof of its declaration: its audit is of the declaration's
  # statement, so it must open the `by` block (comment lines may sit between).
  if ( cd "$pkg" && grep -rlE --include='*.lean' '^[[:space:]]*rung[[:space:]]' "$root" | while IFS= read -r f; do
         awk -v f="$f" '
           /^[[:space:]]*rung[[:space:]]/ {
             if (prev !~ /:=[[:space:]]*by[[:space:]]*$/) { printf "%s:%d: rung does not open its declaration'"'"'s proof\n", f, NR; bad = 1 }
           }
           /^[[:space:]]*$/ || /^[[:space:]]*--/ { next }
           { prev = $0 }
           END { exit bad }' "$f" || true
       done ) | grep .; then
    echo "[FAIL] a proof-ladder rung in $dir/ that is not the whole proof of its declaration"
    scan=1
  fi
  for g in $generated; do
    ex_args+=(--exclude="$(basename "$g")")
  done
  # The generated files translate unit structs such as `Full` as `def ring_buffer.Full := Unit`
  # -- a type, not a claim -- so they are excluded by name; every hand-written file is scanned.
  if ( cd "$pkg" && grep -rnE --include='*.lean' "${ex_args[@]}" "$VACUOUS_RE" "$root" ) ||
     { [ ${#extras[@]} -gt 0 ] && ( cd "$pkg" && grep -nE "$VACUOUS_RE" "${extras[@]}" ); }; then
    echo "[FAIL] vacuous definition (a body that is trivially true) in $dir/"
    scan=1
  fi
  for f in $generated; do
    [ -f "$pkg/$f" ] || { echo "[FAIL] generated file $dir/$f is missing"; scan=1; }
  done
  [ $scan -eq 0 ] || exit 1

  echo "[ok] $name package: lake build (${secs}s), $audited module(s) audited, $(grep -c . "$work/records.$name") record(s); no sorry, no native_decide, no search tactic, no misplaced rung, no vacuous definition"
}

if $clean; then
  rm -rf "$EX/lean/.lake"
fi

# ---------------------------------------------------------------------------------- core package

echo "== core package (lean/) =="
lean_package_stage core "${PKG_DIR[core]}" "${PKG_ROOT[core]}" ""
ran_packages=(core)

# -------------------------------------------------------------------------------- bridge package

echo "== bridge package (aeneas/) =="
bridge_ran=false
if [ "$precheck_mode" = core_only ]; then
  echo "[skip] bridge package (--core-only; not the verification claim)"
else
  # Absent dependencies (Aeneas, Mathlib) are fetched by this stage's lake build (about 7 GB,
  # network): the bridge is part of the gate, so it is never skipped for want of a fetch.
  lean_package_stage bridge "${PKG_DIR[bridge]}" "${PKG_ROOT[bridge]}" \
    "FramedChannelAeneas/Extracted/Types.lean FramedChannelAeneas/Extracted/Funs.lean" \
    GenVectors.lean
  # The hand-written trusted library models: definitions with proved specs, never an axiom.
  if funs_external_forbidden "$EX/aeneas/FramedChannelAeneas/Extracted/FunsExternal.lean"; then
    echo "[FAIL] axiom, sorry, admit or native_decide in aeneas/FramedChannelAeneas/Extracted/FunsExternal.lean"
    exit 1
  fi
  bridge_ran=true
  ran_packages+=(bridge)
fi

# --------------------------------------------------------------------- registry statement hashes

echo "== registry statement hashes =="
hash_args=(--check)
$bridge_ran && hash_args+=(--aeneas)
if ! $bridge_ran; then
  # A skipped bridge package must not be hash-checked behind the gate's back: that would build it.
  hash_args+=(--core-only)
fi
if ! bash "$EX/scripts/refresh-hashes.sh" "${hash_args[@]}"; then
  exit 1
fi

# --------------------------------------------------------------------- specification consistency

# Judge spec-check.sh's records per package that ran: the Challenge library is statement-only,
# its sorry warnings are exactly its statements, it restates exactly the registered names minus the
# shared-proof rows with the registry's hashes, and it depends on no other proof.
echo "== specification consistency =="
spec_args=(--log-dir "$work/spec")
if $bridge_ran; then spec_args+=(--aeneas); else spec_args+=(--core-only); fi
if ! bash "$EX/scripts/spec-check.sh" "${spec_args[@]}" > "$work/spec.out" 2> "$work/spec.err"; then
  cat "$work/spec.err"
  echo "[FAIL] spec-check.sh could not check the Challenge libraries"
  exit 1
fi
LC_ALL=C sort -u <(policy_rows "$POLICY" shared-proof) > "$work/shared"
spec_failures=0
spec_fail() {
  echo "[FAIL] $*"
  spec_failures=$((spec_failures + 1))
}
spec_summary=()
for pkg in "${PACKAGE_NAMES[@]}"; do
  cdir="${PKG_CHALLENGE[$pkg]}"
  if ! in_list "$pkg" "${ran_packages[@]}"; then
    spec_summary+=("$pkg NOT CHECKED (package stage skipped: --core-only)")
    continue
  fi
  awk -v p="$pkg" '$1 == p { $1 = ""; sub(/^ /, ""); print }' "$work/spec.out" > "$work/spec.$pkg"
  # purity
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    spec_fail "$pkg Challenge is not statement-only: $line"
  done <<< "$(grep '^IMPURE ' "$work/spec.$pkg")"
  # sorry warnings: only from the Challenge sources, one per confirmed statement-only theorem
  log="$work/spec/challenge.$pkg.log"
  stmts="$(grep -c '^stmt ' "$work/spec.$pkg")"
  warnings="$(grep -cE "$LEAN_SORRY_MSG" "$log")"
  outside="$(grep -E "$LEAN_SORRY_MSG" "$log" | grep -vE "^warning: ${cdir}(/[A-Za-z0-9]+)?\.lean:" || true)"
  if [ -n "$outside" ]; then
    spec_fail "$pkg Challenge build reports sorry outside ${cdir}: $outside"
  fi
  if [ "$warnings" -ne "$stmts" ]; then
    spec_fail "$pkg Challenge build reports $warnings sorry warning(s), but SpecCheck confirms $stmts statement-only theorem(s)"
  fi
  # names: Challenge + shared-proof rows owned by this package == registered
  registry_hashes "$pkg" > "$work/reghash.$pkg"
  cut -d' ' -f1 "$work/reghash.$pkg" > "$work/regnames.$pkg"
  awk '$1 == "stmt" { print $2 }' "$work/spec.$pkg" | LC_ALL=C sort -u > "$work/challnames.$pkg"
  LC_ALL=C comm -12 "$work/shared" "$work/regnames.$pkg" > "$work/sharedown.$pkg"
  LC_ALL=C sort -u "$work/challnames.$pkg" "$work/sharedown.$pkg" > "$work/specified.$pkg"
  while IFS= read -r n; do
    [ -z "$n" ] && continue
    spec_fail "$n is registered ($pkg), but no ${cdir} module restates it and it is not a shared-proof row"
  done <<< "$(LC_ALL=C comm -23 "$work/regnames.$pkg" "$work/specified.$pkg")"
  while IFS= read -r n; do
    [ -z "$n" ] && continue
    spec_fail "${cdir} restates $n, which the $pkg registry does not register"
  done <<< "$(LC_ALL=C comm -13 "$work/regnames.$pkg" "$work/specified.$pkg")"
  while IFS= read -r n; do
    [ -z "$n" ] && continue
    spec_fail "$n is a shared-proof row but ${cdir} also restates it"
  done <<< "$(LC_ALL=C comm -12 "$work/challnames.$pkg" "$work/sharedown.$pkg")"
  # hashes
  awk '$1 == "stmt" { print $2, $3 }' "$work/spec.$pkg" | LC_ALL=C sort -u > "$work/challhash.$pkg"
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    n="${line%% *}"
    if grep -q "^$n " "$work/reghash.$pkg"; then
      spec_fail "the ${cdir} statement of $n differs from the registered one (Challenge hash ${line##* }, registry hash $(grep "^$n " "$work/reghash.$pkg" | cut -d' ' -f2))"
    fi
  done <<< "$(LC_ALL=C comm -23 "$work/challhash.$pkg" "$work/reghash.$pkg")"
  # proofs inside the specification's imports
  for rec in defs-thm closure-thm; do
    awk -v r="$rec" '$1 == r { print $2 }' "$work/spec.$pkg" | LC_ALL=C sort -u > "$work/$rec.$pkg"
    while IFS= read -r n; do
      [ -z "$n" ] && continue
      case "$rec" in
        defs-thm) spec_fail "$n is a theorem declared in a definitions module but not a shared-proof row of certificate/policy.txt" ;;
        closure-thm) spec_fail "a ${cdir} statement depends on the proof of $n, which is not a shared-proof row (a proof outside the approved specification, or a registered theorem of the other package)" ;;
      esac
    done <<< "$(LC_ALL=C comm -23 "$work/$rec.$pkg" "$work/shared")"
  done
  # every shared-proof row is declared in a definitions module (the bridge imports the core's)
  while IFS= read -r n; do
    [ -z "$n" ] && continue
    spec_fail "shared-proof row $n is not a theorem declared in a definitions module"
  done <<< "$(LC_ALL=C comm -23 "$work/shared" "$work/defs-thm.$pkg")"
  spec_summary+=("$pkg: $stmts restated + $(grep -c . "$work/sharedown.$pkg") shared-proof = $(grep -c . "$work/regnames.$pkg") registered, hashes equal, $(grep -c '^digest ' "$work/spec.$pkg") module digest(s)")
done
if [ $spec_failures -ne 0 ]; then
  echo "check.sh: $spec_failures specification consistency failure(s)"
  exit 1
fi
for line in "${spec_summary[@]}"; do
  echo "[ok] specification consistency, $line"
done

# ------------------------------------------------------------------------- selection consistency

# The approval-independent half of Select: candidates.txt is well-formed and the approval digests
# are computed; with the bridge package, every reached extracted item is an in-subset candidate (or
# a loop part, trait record or foreign library item) and every non-derived in-subset candidate is
# reached.
echo "== selection consistency =="
# shellcheck source=scripts/lib/approval-digests.sh
. "$EX/scripts/lib/approval-digests.sh"
cand_file="$CERT/candidates.txt"
if [ ! -f "$cand_file" ]; then
  echo "[FAIL] certificate/candidates.txt is missing; generate it with: bash scripts/refresh-candidates.sh"
  exit 1
fi
if ! awk -F'\t' '
    /^#/ { next }
    NF != 8 { printf "[FAIL] certificate/candidates.txt:%d: %d columns, expected 8\n", NR, NF; bad = 1; next }
    $4 !~ /^(pub|priv)$/ || $5 !~ /^(fn|trait-impl|const)$/ || $6 !~ /^(-|derived:[A-Za-z]+)$/ ||
      $7 !~ /^(in-subset|excluded)$/ || ($7 == "in-subset" && $8 != "-") || ($7 == "excluded" && $8 == "-") {
      printf "[FAIL] certificate/candidates.txt:%d: malformed row\n", NR; bad = 1; next
    }
    $1 != "-" { if (seen[$1]++) { printf "[FAIL] certificate/candidates.txt:%d: duplicate Lean name %s\n", NR, $1; bad = 1 } }
    { rows++ }
    END { if (rows == 0) { print "[FAIL] certificate/candidates.txt has no rows"; bad = 1 }; exit bad }
  ' "$cand_file"; then
  exit 1
fi
sel_src="$(source_sha256 "$EX")" || { echo "[FAIL] could not digest rust/src, rust/Cargo.toml, rust/Cargo.lock"; exit 1; }
sel_cand="$(candidates_sha256 "$EX")"
insubset_candidates "$cand_file" > "$work/cand.insubset"
awk -F'\t' '!/^#/ && $7 == "excluded" && $1 != "-" { print $1 }' "$cand_file" | LC_ALL=C sort -u > "$work/cand.excluded"
awk -F'\t' '!/^#/ && $7 == "in-subset" && $6 == "-" { print $1 }' "$cand_file" | LC_ALL=C sort -u > "$work/cand.nonderived"
echo "[ok] candidates well-formed ($(grep -c . "$work/cand.insubset") in-subset, $(grep -c . "$work/cand.excluded") excluded); source_sha256 $sel_src, candidates_sha256 $sel_cand"
if ! $bridge_ran; then
  echo "[skip] selection reach check: NOT CHECKED (bridge package not built: --core-only)"
else
  awk '$1 == "bridge" && $2 == "reached" { print $3 }' "$work/spec.out" | LC_ALL=C sort -u > "$work/reached"
  sel_failures=0
  parts=0; records_n=0; foreign=()
  while IFS= read -r n; do
    [ -z "$n" ] && continue
    if grep -qxF "$n" "$work/cand.insubset"; then
      continue
    fi
    if grep -qxF "$n" "$work/cand.excluded"; then
      echo "[FAIL] a registered statement is about $n, an excluded candidate ($(awk -F'\t' -v n="$n" '$1 == n { print $8 }' "$cand_file"))"
      sel_failures=$((sel_failures + 1))
      continue
    fi
    base="${n%.body}"
    while [[ "$base" =~ _loop[0-9]*$ ]]; do base="${base%_loop*}"; done
    if [ "$base" != "$n" ] && grep -qxF "$base" "$work/cand.insubset"; then
      parts=$((parts + 1))
    elif awk -v p="$n." 'index($0, p) == 1 { f = 1 } END { exit !f }' "$work/cand.insubset"; then
      records_n=$((records_n + 1))
    else
      foreign+=("$n")
    fi
  done < "$work/reached"
  while IFS= read -r n; do
    [ -z "$n" ] && continue
    echo "[FAIL] in-subset candidate $n is not derived, but no registered statement is about it (nothing specifies it)"
    sel_failures=$((sel_failures + 1))
  done <<< "$(LC_ALL=C comm -23 "$work/cand.nonderived" "$work/reached")"
  if [ $sel_failures -ne 0 ]; then
    echo "check.sh: $sel_failures selection consistency failure(s)"
    exit 1
  fi
  echo "[ok] selection reach: $(LC_ALL=C comm -12 "$work/cand.insubset" "$work/reached" | grep -c .) in-subset candidates reached, every non-derived one among them; $(LC_ALL=C comm -23 "$work/cand.insubset" "$work/reached" | grep -c .) unreached (all derived); also reached: $parts loop part(s), $records_n trait record(s), ${#foreign[@]} foreign item(s)${foreign[*]:+: ${foreign[*]}}"
fi

# -------------------------------------------------------------------------- differential vectors

# Regenerate by evaluating the extraction (aeneas/GenVectors.lean) and diff against
# certificate/vectors.txt, which this stage never writes (refresh-vectors.sh does). Needs the
# bridge package; otherwise NOT CHECKED, and the file is covered only by cargo test.
echo "== differential vectors =="
if ! $bridge_ran; then
  echo "[skip] differential vectors: NOT CHECKED (bridge package not built: --core-only)"
else
  gen_out="$work/vectors.out"
  gen_log="$work/vectors.log"
  if ! ( cd "$EX/aeneas" && lake env lean --run GenVectors.lean ) > "$gen_out" 2> "$gen_log"; then
    echo "[FAIL] lake env lean --run GenVectors.lean (in aeneas/)"
    cat "$gen_out" "$gen_log" | tail -20
    exit 1
  fi
  if genvectors_messages "$gen_out" "$gen_log"; then
    echo "[FAIL] aeneas/GenVectors.lean emitted compiler messages (a warning or a sorry)"
    exit 1
  fi
  if [ ! -f "$CERT/vectors.txt" ]; then
    echo "[FAIL] certificate/vectors.txt is missing; run 'bash scripts/refresh-vectors.sh'"
    exit 1
  fi
  if ! diff -u "$CERT/vectors.txt" "$gen_out" > /dev/null; then
    echo "[FAIL] certificate/vectors.txt no longer matches what evaluating the extraction computes"
    diff -u "$CERT/vectors.txt" "$gen_out" | sed -n '1,60p'
    echo "  Every changed record is a translated behavior that changed. Re-read the diff, then"
    echo "  regenerate with:"
    echo "    bash scripts/refresh-vectors.sh"
    exit 1
  fi
  vector_records="$(grep -cvE '^[[:space:]]*(#|$)' "$gen_out")"
  echo "[ok] differential vectors ($vector_records records match the evaluated extraction)"
fi

# ----------------------------------------------------------------------------------- axiom audit

# From lean/, so elan resolves the pinned toolchain rather than whatever its default is.
lean_version="$(cd "$EX/lean" && lean --version)"

aggregates=("${CORE_AGGREGATES[@]}")
$bridge_ran && aggregates+=("${BRIDGE_AGGREGATES[@]}")

# Buffered into $work rather than written straight to $AXIOMS: the audit's own verdict (the
# violation-counting loop below) is not known yet at this point, and a run that FAILS the audit
# must never leave the failing content in a freshly identity-matching axioms.txt (D7) -- matching
# ladder.txt/countermodels.txt/digests.txt, which are each written only after their own failure
# check has already returned. Moved into place near the bottom of this section, only on a pass.
axioms_buffer="$work/axioms.generated"
{
  echo "# framed_channel axiom audit (generated by check.sh; do not edit)"
  echo "lean: $lean_version"
  echo "certificate identity: $IDENTITY"
  echo "trusted axioms: ${TRUSTED[*]}"
  echo "flagged compiler-trusting declarations (allow-list): ${FLAGGED[*]}"
  echo "bank aggregates (inherit the flagged row's axioms by construction): ${aggregates[*]}"
  # Grouped by package, then by module in a FIXED (sorted) order: Lake's build order varies
  # between runs, so build order would make this generated file churn with nothing changed.
  for pkg in "${PACKAGE_NAMES[@]}"; do
    dir="${PKG_DIR[$pkg]}"
    echo
    if ! in_list "$pkg" "${ran_packages[@]}"; then
      echo "# package: $pkg ($dir/) -- NOT AUDITED in this run: the $pkg package stage was skipped (--core-only; this file is not the verification claim)"
      continue
    fi
    echo "# package: $pkg ($dir/)"
    while IFS= read -r mod; do
      [ -z "$mod" ] && continue
      echo
      echo "## $dir/$mod"
      grep "^info: $mod:" "$work/records.$pkg" | sed 's|^info: [^:]*:[0-9]*:[0-9]*: ||'
    done < "$work/modules.$pkg"
  done
} > "$axioms_buffer"

records="$work/records.all"
for pkg in "${ran_packages[@]}"; do
  cat "$work/records.$pkg"
done > "$records"

echo "== axiom audit =="
violations=0
while IFS= read -r line; do
  decl="$(echo "$line" | sed -n "s|.*'\\([^']*\\)'.*|\\1|p")"
  [ -z "$decl" ] && continue
  case "$line" in
    *"does not depend on any axioms"*) continue ;;
  esac
  axlist="$(axiom_list "$line")"
  IFS=',' read -r -a axs <<< "$axlist"
  for ax in "${axs[@]}"; do
    [ -z "$ax" ] && continue
    in_list "$ax" "${TRUSTED[@]}" && continue
    if [ "$ax" = "sorryAx" ]; then
      echo "[FAIL] $decl depends on sorryAx"
      violations=$((violations + 1))
      continue
    fi
    if is_compiler_trusting "$ax"; then
      in_list "$decl" "${FLAGGED[@]}" && continue
      if in_list "$decl" "${aggregates[@]}" && [ ${#FLAGGED[@]} -gt 0 ]; then
        continue
      fi
      echo "[FAIL] $decl depends on $ax but is not on the flagged allow-list"
      violations=$((violations + 1))
      continue
    fi
    echo "[FAIL] $decl depends on $ax, which is outside the trusted set"
    violations=$((violations + 1))
  done
done < "$records"

# The allow-lists must be exactly what is used: an entry with no record, or a flagged row whose
# record carries no recognised compiler-trusting axiom (say, after a helper-axiom renaming), fails.
for f in "${FLAGGED[@]}"; do
  if ! grep -q "'$f'" "$records"; then
    echo "[FAIL] flagged row $f has no axiom record; remove its row from certificate/policy.txt"
    violations=$((violations + 1))
  fi
done
for f in "${aggregates[@]}"; do
  if ! grep -q "'$f'" "$records"; then
    echo "[FAIL] bank aggregate $f has no axiom record; remove it from CORE_AGGREGATES or BRIDGE_AGGREGATES in check.sh"
    violations=$((violations + 1))
  fi
done
for f in "${FLAGGED[@]}"; do
  frec="$(axiom_list "$(grep "'$f' depends on axioms" "$records")")"
  carries=false
  IFS=',' read -r -a faxs <<< "$frec"
  for ax in "${faxs[@]}"; do
    if [ -n "$ax" ] && is_compiler_trusting "$ax"; then carries=true; fi
  done
  if ! $carries; then
    echo "[FAIL] flagged row $f carries no compiler-trusting axiom; remove its row from certificate/policy.txt"
    violations=$((violations + 1))
  fi
done

if [ $violations -ne 0 ]; then
  echo "check.sh: $violations axiom-audit violation(s); see the [FAIL] lines above -- the audit failed, so $AXIOMS was NOT rewritten (it still names whatever passing run last wrote it, if any)"
  exit 1
fi
mv "$axioms_buffer" "$AXIOMS"
if [ "$precheck_mode" = core_only ]; then
  echo "[ok] axiom audit ($(grep -c . "$records") records over: ${ran_packages[*]}; the bridge package is NOT AUDITED ($(precheck_flag)); nothing written under certificate/)"
elif [ "$precheck_mode" = committed_extraction ]; then
  echo "[ok] axiom audit ($(grep -c . "$records") records over: ${ran_packages[*]}; nothing written under certificate/ ($(precheck_flag)))"
else
  echo "[ok] axiom audit ($(grep -c . "$records") records over: ${ran_packages[*]}; written to certificate/axioms.txt)"
fi

# ---------------------------------------------------------------------------------- proof ladder

# The build checked each proof-ladder record where it was made (lean/FramedChannel/Ladder.lean);
# this stage checks the records are complete and consistent with the registry, policy.txt and the
# axiom records. Bridge rows are not laddered and are reported NOT CHECKED.
echo "== proof ladder =="
ladder_failures=0
ladder_fail() {
  echo "[FAIL] $*"
  ladder_failures=$((ladder_failures + 1))
}
LADDER_METHODS_RE='^(decide|simp|omega|grind|retrieval|bv_decide|manual|instance)$'
grep '^ladder ' "$work/ladder.core" | sed 's/^ladder //' | LC_ALL=C sort > "$work/ladder.records"
grep '^countermodel ' "$work/ladder.core" | sed 's/^countermodel //' | LC_ALL=C sort > "$work/cm.records"
if grep -q . "$work/ladder.bridge" 2>/dev/null; then
  ladder_fail "the bridge package emitted proof-ladder records, but only the core registry is laddered: $(head -3 "$work/ladder.bridge" | tr '\n' ';')"
fi

# names and methods
cut -d' ' -f1 "$work/ladder.records" | LC_ALL=C sort > "$work/ladder.names"
registry_names core > "$work/ladder.registered"
while IFS= read -r n; do
  [ -z "$n" ] && continue
  ladder_fail "$n has more than one proof-ladder record"
done <<< "$(uniq -d "$work/ladder.names")"
while IFS= read -r n; do
  [ -z "$n" ] && continue
  ladder_fail "$n is registered in the core registry, but has no proof-ladder record (wrap its proof in rung, or record it with ladder_record%)"
done <<< "$(LC_ALL=C comm -23 "$work/ladder.registered" <(LC_ALL=C sort -u "$work/ladder.names"))"
while IFS= read -r n; do
  [ -z "$n" ] && continue
  ladder_fail "$n has a proof-ladder record, but the core registry does not register it"
done <<< "$(LC_ALL=C comm -13 "$work/ladder.registered" <(LC_ALL=C sort -u "$work/ladder.names"))"
while IFS= read -r line; do
  [ -z "$line" ] && continue
  n="${line%% *}"; rest="${line#* }"; m="${rest%% *}"; q=""
  [ "$rest" != "$m" ] && q="${rest#* }"
  if ! [[ "$m" =~ $LADDER_METHODS_RE ]]; then
    ladder_fail "$n has an unknown proof-ladder method '$m'"
  fi
  case "$q" in
    ""|"(excluding bv_decide)"|"(post-declaration; retrieval audit not run)") ;;
    *) ladder_fail "$n has an unknown proof-ladder qualifier '$q'" ;;
  esac
done < "$work/ladder.records"

# post-declaration theorem records == the core shared-proof rows
grep ' (post-declaration; retrieval audit not run)$' "$work/ladder.records" | cut -d' ' -f1 | LC_ALL=C sort -u > "$work/ladder.post"
LC_ALL=C comm -12 "$work/shared" "$work/ladder.registered" > "$work/ladder.sharedcore"
if ! diff -q "$work/ladder.post" "$work/ladder.sharedcore" > /dev/null; then
  ladder_fail "the post-declaration theorem records ($(tr '\n' ' ' < "$work/ladder.post")) differ from the core shared-proof rows of certificate/policy.txt ($(tr '\n' ' ' < "$work/ladder.sharedcore")); every other registered theorem must be proved through rung"
fi

# bv_decide records == flagged rows == registered declarations with a compiler-trusting record
awk '$2 == "bv_decide" { print $1 }' "$work/ladder.records" | LC_ALL=C sort -u > "$work/ladder.bv"
printf '%s\n' "${FLAGGED[@]}" | sed '/^$/d' | LC_ALL=C sort -u > "$work/ladder.flagged"
: > "$work/ladder.trusting"
while IFS= read -r line; do
  decl="$(echo "$line" | sed -n "s|.*'\\([^']*\\)' depends on axioms.*|\\1|p")"
  [ -z "$decl" ] && continue
  grep -qxF "$decl" "$work/ladder.registered" || continue
  axlist="$(axiom_list "$line")"
  IFS=',' read -r -a axs <<< "$axlist"
  for ax in "${axs[@]}"; do
    if [ -n "$ax" ] && { in_list "$ax" "${COMPILER_TRUSTING[@]}" || [[ "$ax" =~ \._native\.bv_decide\.ax_[0-9]+_[0-9]+$ ]]; }; then
      echo "$decl" >> "$work/ladder.trusting"
      break
    fi
  done
done < "$work/records.core"
LC_ALL=C sort -u -o "$work/ladder.trusting" "$work/ladder.trusting"
if ! diff -q "$work/ladder.bv" "$work/ladder.flagged" > /dev/null; then
  ladder_fail "the bv_decide records ($(tr '\n' ' ' < "$work/ladder.bv")) differ from the flagged rows of certificate/policy.txt ($(tr '\n' ' ' < "$work/ladder.flagged"))"
fi
if ! diff -q "$work/ladder.bv" "$work/ladder.trusting" > /dev/null; then
  ladder_fail "the bv_decide records ($(tr '\n' ' ' < "$work/ladder.bv")) differ from the registered declarations whose axiom record is compiler-trusting ($(tr '\n' ' ' < "$work/ladder.trusting"))"
fi

# countermodels: one record per refuted% line, each kernel-only
( cd "$EX/lean" && grep -rhE --include='*.lean' '^[[:space:]]*refuted%[[:space:]]' FramedChannel ) |
  awk '{ print $2, $3, $4 }' > "$work/cm.src"
awk '{ print $1 }' "$work/cm.src" | LC_ALL=C sort > "$work/cm.src.short"
cut -d' ' -f1 "$work/cm.records" | sed 's/^FramedChannel\.//' | LC_ALL=C sort > "$work/cm.rec.short"
if ! diff -q "$work/cm.src.short" "$work/cm.rec.short" > /dev/null || [ -n "$(uniq -d "$work/cm.rec.short")" ]; then
  ladder_fail "the countermodel records ($(tr '\n' ' ' < "$work/cm.rec.short")) do not correspond one to one with the refuted% lines ($(tr '\n' ' ' < "$work/cm.src.short"))"
fi
while read -r cand false_thm search_thm; do
  [ -z "$cand" ] && continue
  for t in "$false_thm" "$search_thm"; do
    rec="$(grep -E "^info: FramedChannel/Evidence/[^:]*:[0-9]+:[0-9]+: 'FramedChannel\\.$t' (depends on axioms|does not depend)" "$work/records.core" || true)"
    if [ -z "$rec" ]; then
      ladder_fail "countermodel $cand: $t has no axiom record in an Evidence module (add #print axioms $t)"
      continue
    fi
    axlist="$(axiom_list "$rec")"
    IFS=',' read -r -a axs <<< "$axlist"
    for ax in "${axs[@]}"; do
      [ -z "$ax" ] && continue
      in_list "$ax" "${TRUSTED[@]}" || ladder_fail "countermodel $cand: $t depends on $ax, outside the trusted set (countermodels are kernel-only)"
    done
  done
done < "$work/cm.src"
while IFS= read -r line; do
  [ -z "$line" ] && continue
  ladder_fail "an Evidence declaration is compiler-trusting or flagged: $line"
done <<< "$(grep '^info: FramedChannel/Evidence/' "$work/records.core" | grep -E 'ofReduceBool|trustCompiler|_native\.' || true)"
for f in "${FLAGGED[@]}"; do
  if grep -q "^info: FramedChannel/Evidence/.*'$f'" "$work/records.core"; then
    ladder_fail "flagged row $f is declared in an Evidence module"
  fi
done

if [ $ladder_failures -ne 0 ]; then
  echo "check.sh: $ladder_failures proof-ladder failure(s)"
  exit 1
fi

method_counts="$(awk '{ c[$2]++ } END { n = split("decide simp omega grind retrieval bv_decide manual instance", o, " "); s = ""; for (i = 1; i <= n; i++) if (c[o[i]]) s = s (s ? ", " : "") c[o[i]] " " o[i]; print s }' "$work/ladder.records")"
{
  echo "# framed_channel proof ladder (generated by check.sh; do not edit)"
  echo "# certificate identity: $IDENTITY"
  echo "# One record per registered core theorem: <declaration> <method> [qualifier]. Each record was"
  echo "# made where the theorem is declared, by lean/FramedChannel/Ladder.lean, which checks that the"
  echo "# proof script is in the method's syntax class and that no strictly cheaper rung closes the goal."
  echo "# Rungs, cheapest first: decide < simp < omega < grind < retrieval < bv_decide < manual."
  echo "#   bv_decide  compiler-trusting (the flagged row of policy.txt)"
  echo "#   manual     a script a person or an outside agent wrote; the gate cannot tell which"
  echo "#   instance   a class instance, assembled field by field; no audit is claimed"
  echo "#   (post-declaration; retrieval audit not run)  a shared-proof row, audited after the fact"
  echo "# There is no AI-prover rung: none is demonstrated in this repository."
  echo "# Bridge package rows (aeneas/): NOT CHECKED (not laddered)."
  echo "# summary: $(grep -c . "$work/ladder.records") records: $method_counts"
  cat "$work/ladder.records"
} > "$LADDER"
{
  echo "# framed_channel refuted candidate statements (generated by check.sh; do not edit)"
  echo "# certificate identity: $IDENTITY"
  echo "# <candidate> <witness>: the candidate is a Prop definition in lean/FramedChannel/Evidence/,"
  echo "# refuted in the kernel at the witness, which is the first failure of a kernel-checked search"
  echo "# over an explicit enumeration and is read off that search theorem, never typed by hand."
  cat "$work/cm.records"
} > "$COUNTERMODELS"
if [ "$precheck_mode" != full ]; then
  echo "[ok] proof ladder: $(grep -c . "$work/ladder.records") core records equal the registry ($method_counts); bv_decide == flagged == compiler-trusting records; post-declaration == shared-proof rows; $(grep -c . "$work/cm.records") countermodel(s), kernel-only; nothing written under certificate/ ($(precheck_flag))"
else
  echo "[ok] proof ladder: $(grep -c . "$work/ladder.records") core records equal the registry ($method_counts); bv_decide == flagged == compiler-trusting records; post-declaration == shared-proof rows; $(grep -c . "$work/cm.records") countermodel(s), kernel-only; written to certificate/ladder.txt and certificate/countermodels.txt"
fi
echo "[skip] proof ladder, bridge package: NOT CHECKED (not laddered; $(registry_rows bridge | grep -c .) bridge rows)"

# -------------------------------------------------------------------------- manifest cross-check

# The manifests' proofs: names equal the registered names; supporting: names have axiom records;
# specification:, toolchain: and independent_recheck blocks are structurally complete. A name owned
# (by source, not by namespace) by a skipped package is UNAUDITED, never passed or failed.
# certificate/shared.yaml holds the toolchain and independent_recheck content every manifest
# shares (not itself a manifest, and not a certificate-identity input; see README.md); every
# manifest's toolchain: and independent_recheck: must point at it and restate none of it. A small
# revision lint (manifest_revision_tokens) also fails on any restated toolchain revision in a
# manifest or in shared.yaml.
echo "== manifest cross-check =="
SHARED="$CERT/shared.yaml"
mapfile -t MANIFESTS < <(printf '%s\n' "$CERT"/*.yaml | grep -vxF -e "$CERT/approvals.yaml" -e "$SHARED")

# manifest_section FILE KEY: every line under the top-level YAML key KEY of FILE (its own heading
# line excluded), until the next top-level key or EOF. The shared section-scoping half of every
# manifest scan below; each caller applies its own field extraction or membership test on top.
manifest_section() {
  awk -v key="$2" '
    /^[A-Za-z_][A-Za-z0-9_]*:/ { section = $0; sub(/:.*/, "", section); next }
    section == key { print }' "$1"
}

# manifest_names KEY: every `- name:` entry under the top-level KEY of every manifest.
manifest_names() {
  local key="$1" f
  for f in "${MANIFESTS[@]}"; do manifest_section "$f" "$key"; done | awk '
    /^[[:space:]]*-[[:space:]]+name:[[:space:]]/ {
      n = $0; sub(/.*name:[[:space:]]*/, "", n); sub(/[[:space:]]+$/, "", n); print n
    }' | LC_ALL=C sort -u
}

manifest_names proofs > "$work/proofs"
manifest_names supporting > "$work/supporting"
registry_names core > "$work/registered.core"
registry_names bridge > "$work/registered.bridge"
LC_ALL=C sort -u "$work/registered.core" "$work/registered.bridge" > "$work/registered"

manifest_failures=0
unaudited=0
fail_each manifest_failures 'a manifest certifies %s under proofs:, but no registry registers it (add a register%% row, or move it to supporting: if it is not an obligation)' \
  <<< "$(LC_ALL=C comm -23 "$work/proofs" "$work/registered")"
fail_each manifest_failures '%s is registered, but no manifest lists it under proofs:' \
  <<< "$(LC_ALL=C comm -13 "$work/proofs" "$work/registered")"
fail_each manifest_failures '%s is listed under both proofs: and supporting:' \
  <<< "$(LC_ALL=C comm -12 "$work/proofs" "$work/supporting")"

# owner_of_proof NAME / owner_of_supporting NAME: the package that owns a name, by source.
owner_of_proof() {
  if grep -qxF "$1" "$work/registered.bridge"; then echo bridge; else echo core; fi
}
owner_of_supporting() {
  if grep -rqE --include='*.lean' "^[[:space:]]*#print axioms $(printf '%s' "$1" | sed 's/\./\\./g')[[:space:]]*$" \
       "$EX/aeneas/FramedChannelAeneas"; then
    echo bridge
  else
    echo core
  fi
}

check_record() {
  local decl="$1" owner="$2" what="$3"
  if ! in_list "$owner" "${ran_packages[@]}"; then
    unaudited=$((unaudited + 1))
    return
  fi
  if ! grep -q "'$decl'" "$records"; then
    echo "[FAIL] a manifest names $decl under $what, which has no record in axioms.txt"
    manifest_failures=$((manifest_failures + 1))
  fi
}
while IFS= read -r decl; do
  [ -z "$decl" ] && continue
  check_record "$decl" "$(owner_of_proof "$decl")" proofs:
done < "$work/proofs"
while IFS= read -r decl; do
  [ -z "$decl" ] && continue
  check_record "$decl" "$(owner_of_supporting "$decl")" supporting:
done < "$work/supporting"

# specification: every named Challenge module exists, and every proofs: name is restated in one of
# them (the specification stage's `stmt` records carry the module) or is a shared-proof row.
spec_checked=0
for manifest in "${MANIFESTS[@]}"; do
  mname="certificate/$(basename "$manifest")"
  manifest_section "$manifest" specification | awk '
    /^[[:space:]]*-[[:space:]]+challenge:[[:space:]]/ {
      n = $0; sub(/.*challenge:[[:space:]]*/, "", n); sub(/[[:space:]]+$/, "", n); print n
    }' | LC_ALL=C sort -u > "$work/mspec"
  if ! grep -q . "$work/mspec"; then
    echo "[FAIL] $mname has no specification: block naming the Challenge modules its proofs: are checked against"
    manifest_failures=$((manifest_failures + 1))
    continue
  fi
  while IFS= read -r m; do
    if ! f="$(challenge_file "$m")" || [ ! -f "$EX/$f" ]; then
      echo "[FAIL] $mname names $m under specification:, which is not a Challenge module"
      manifest_failures=$((manifest_failures + 1))
    fi
  done < "$work/mspec"
  manifest_section "$manifest" proofs | awk '
    /^[[:space:]]*-[[:space:]]+name:[[:space:]]/ {
      n = $0; sub(/.*name:[[:space:]]*/, "", n); sub(/[[:space:]]+$/, "", n); print n
    }' | LC_ALL=C sort -u > "$work/mproofs"
  while IFS= read -r decl; do
    [ -z "$decl" ] && continue
    grep -qxF "$decl" "$work/shared" && continue
    owner_pkg="$(owner_of_proof "$decl")"
    if ! in_list "$owner_pkg" "${ran_packages[@]}"; then
      unaudited=$((unaudited + 1))
      continue
    fi
    owner_mod="$(awk -v p="$owner_pkg" -v n="$decl" '$1 == p && $2 == "stmt" && $3 == n { print $5 }' "$work/spec.out")"
    if [ -z "$owner_mod" ] || ! grep -qxF "$owner_mod" "$work/mspec"; then
      echo "[FAIL] $mname certifies $decl, which is restated in ${owner_mod:-no Challenge module}, not in a module its specification: block names"
      manifest_failures=$((manifest_failures + 1))
    fi
    spec_checked=$((spec_checked + 1))
  done < "$work/mproofs"
done

# toolchain.certificate_identity: and trust.G0_checker.independent_recheck's comparator,
# lean4lean and leanchecker entries (each with a verdict and record certificate/recheck.txt) now
# live once, in certificate/shared.yaml; every manifest's toolchain: and independent_recheck:
# must point at it (shared: certificate/shared.yaml) and restate none of those entries. Neither
# block, anywhere, names a repository_commit:.
toolchain_identity_block() {
  manifest_section "$1" toolchain
}
independent_recheck_block() {
  awk '
    /^[A-Za-z_][A-Za-z0-9_]*:/ { top = $0; sub(/:.*/, "", top); g0 = 0; ir = 0; next }
    top != "trust" { next }
    /^  [A-Za-z0-9_]+:/ { g0 = ($0 ~ /^  G0_checker:/); ir = 0; next }
    g0 && /^    [A-Za-z0-9_]+:/ { ir = ($0 ~ /^    independent_recheck:/); if (ir) print "BLOCK"; next }
    g0 && ir && /^      [A-Za-z0-9_]+:/ { key = $1; sub(/:$/, "", key); print "KEY " key; next }
    g0 && ir && /^        record:/ { print "RECORD " key " " $2; next }
    g0 && ir && /^        verdict:/ { print "VERDICT " key " " $2; next }
  ' "$1"
}
# manifest_revision_tokens FILE: every token in FILE (comment lines excluded) shaped like a
# restated toolchain revision -- a hex revision (7-40 hex chars, at least one digit and one
# letter, so a plain decimal number never matches) or a version triple (vN.N.N or vN.N.N-rcN). A
# manifest or shared.yaml states none of these; it points at a pin file or generated record.
manifest_revision_tokens() {
  grep -v '^[[:space:]]*#' "$1" \
    | grep -oE '\b[0-9a-f]{7,40}\b|\bv?[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?\b' \
    | awk '
        /^v?[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$/ { print; next }
        /[0-9]/ && /[a-f]/ { print }
      '
}

if [ ! -f "$SHARED" ]; then
  echo "[FAIL] $SHARED is missing; every manifest's toolchain: and independent_recheck: point at it"
  manifest_failures=$((manifest_failures + 1))
else
  tc="$(toolchain_identity_block "$SHARED")"
  if ! printf '%s\n' "$tc" | grep -qE '^[[:space:]]+certificate_identity:[[:space:]]'; then
    echo "[FAIL] certificate/shared.yaml has no toolchain.certificate_identity: pointer to the identity line of digests.txt"
    manifest_failures=$((manifest_failures + 1))
  fi
  ir="$(independent_recheck_block "$SHARED")"
  if ! printf '%s\n' "$ir" | grep -qx BLOCK; then
    echo "[FAIL] certificate/shared.yaml has no trust.G0_checker.independent_recheck: block"
    manifest_failures=$((manifest_failures + 1))
  else
    for key in comparator lean4lean leanchecker; do
      if ! printf '%s\n' "$ir" | grep -qx "KEY $key"; then
        echo "[FAIL] certificate/shared.yaml: trust.G0_checker.independent_recheck has no $key: entry"
        manifest_failures=$((manifest_failures + 1))
        continue
      fi
      if ! printf '%s\n' "$ir" | grep -qx "RECORD $key certificate/recheck.txt"; then
        echo "[FAIL] certificate/shared.yaml: independent_recheck.$key does not name record: certificate/recheck.txt"
        manifest_failures=$((manifest_failures + 1))
      fi
      if ! printf '%s\n' "$ir" | grep -qE "^VERDICT $key (verified|validated|trusted)$"; then
        echo "[FAIL] certificate/shared.yaml: independent_recheck.$key has no verdict: from the fixed vocabulary"
        manifest_failures=$((manifest_failures + 1))
      fi
    done
  fi
  if grep -qE '^[[:space:]]*repository_commit:' "$SHARED"; then
    echo "[FAIL] certificate/shared.yaml names a repository_commit:; the certificate names content (certificate_identity:), not a commit"
    manifest_failures=$((manifest_failures + 1))
  fi
fi

for manifest in "${MANIFESTS[@]}"; do
  mname="certificate/$(basename "$manifest")"
  tc="$(toolchain_identity_block "$manifest")"
  if ! printf '%s\n' "$tc" | grep -qE '^[[:space:]]+shared:[[:space:]]+certificate/shared\.yaml[[:space:]]*$'; then
    echo "[FAIL] $mname's toolchain: does not carry shared: certificate/shared.yaml"
    manifest_failures=$((manifest_failures + 1))
  fi
  ir="$(independent_recheck_block "$manifest")"
  if ! printf '%s\n' "$ir" | grep -qx BLOCK; then
    echo "[FAIL] $mname has no trust.G0_checker.independent_recheck: block"
    manifest_failures=$((manifest_failures + 1))
  else
    if ! printf '%s\n' "$ir" | grep -qx "KEY shared"; then
      echo "[FAIL] $mname's independent_recheck: does not carry shared: certificate/shared.yaml"
      manifest_failures=$((manifest_failures + 1))
    fi
    for key in comparator lean4lean leanchecker; do
      if printf '%s\n' "$ir" | grep -qx "KEY $key"; then
        echo "[FAIL] $mname's independent_recheck: restates $key: itself; point at certificate/shared.yaml instead"
        manifest_failures=$((manifest_failures + 1))
      fi
    done
  fi
  if grep -qE '^[[:space:]]*repository_commit:' "$manifest"; then
    echo "[FAIL] $mname names a repository_commit:; the certificate names content (certificate_identity:), not a commit"
    manifest_failures=$((manifest_failures + 1))
  fi
done

for f in "${MANIFESTS[@]}" "$SHARED"; do
  fname="certificate/$(basename "$f")"
  while IFS= read -r tok; do
    [ -z "$tok" ] && continue
    echo "[FAIL] $fname: restates a toolchain revision ($tok); point at nix/aeneas-pin.json, lean/lean-toolchain, rust-toolchain.toml or certificate/{candidates,recheck}.txt instead"
    manifest_failures=$((manifest_failures + 1))
  done < <(manifest_revision_tokens "$f")
done

if [ $manifest_failures -ne 0 ]; then
  echo "check.sh: $manifest_failures manifest cross-check failure(s)"
  exit 1
fi
summary="$(grep -c . "$work/proofs") proofs: entries equal the $(grep -c . "$work/registered") registered names; $(grep -c . "$work/supporting") supporting: entries; $spec_checked proofs: entries restated in a Challenge module their manifest's specification: block names"
if [ $unaudited -ne 0 ]; then
  echo "[ok] manifest cross-check ($summary; $unaudited name(s) owned by the bridge package are UNAUDITED in this run: --core-only)"
else
  echo "[ok] manifest cross-check ($summary; every entry has an axiom record)"
fi

# --------------------------------------------------------------------------- independent recheck

# With --recheck: Comparator in fresh clean rooms and a kernel replay (Lean4Lean, leanchecker),
# writing certificate/recheck.txt. Without it nothing runs and the stored record is reported
# current or STALE, never passed. What each checker establishes: certificate/README.md.
echo "== independent recheck =="
if ! $recheck; then
  if [ ! -f "$RECHECK" ]; then
    echo "[skip] independent recheck NOT RUN (pass --recheck)"
  else
    rec_id="$(sed -n -E 's/^certificate identity: (sha256:[0-9a-f]{64})$/\1/p' "$RECHECK" | head -1)"
    if [ "$rec_id" != "$IDENTITY" ]; then
      echo "[skip] recheck.txt is for identity ${rec_id:-(none)}, the tree is $IDENTITY: STALE, not a pass (re-run with --recheck)"
    elif grep -qE '^verdict: [^ ]+ [^ ]+ FAIL( |$)' "$RECHECK"; then
      echo "[skip] recheck.txt is current but records a FAIL verdict: not a pass (re-run with --recheck)"
    elif ! grep -qx 'record: complete' "$RECHECK"; then
      echo "[skip] recheck.txt is current but PARTIAL, not a pass ($(sed -n 's/^record: //p' "$RECHECK" | head -1); re-run with --recheck on a platform where every verdict runs, or adopt a CI-produced record: scripts/adopt-recheck.sh)"
    else
      echo "[ok] recheck.txt is current (identity matches): $(grep -cE '^verdict: [^ ]+ [^ ]+ (OK|EXPECTED-REJECTION)( |$)' "$RECHECK") verdict(s) OK or EXPECTED-REJECTION, $(grep -cE '^verdict: [^ ]+ [^ ]+ NOT-RUN( |$)' "$RECHECK") NOT RUN"
    fi
  fi
else
  if [ -z "${_RECHECK_REVS_SOURCED:-}" ]; then
    # shellcheck source=scripts/lib/recheck-revs.sh
    . "$EX/scripts/lib/recheck-revs.sh"
  fi
  if ! recheck_rev_coherence > "$work/recheck.coherence" 2>&1; then
    cat "$work/recheck.coherence"
    echo "check.sh: the independent recheck's pinned revisions disagree; see above"
    exit 1
  fi
  cat "$work/recheck.coherence"
  # --bridge is unconditional here: --recheck is refused above (check.sh:233,243) in combination
  # with both --core-only and --committed-extraction, the only two modes that ever leave
  # bridge_ran false, so bridge_ran is always true by this point.
  kernel_args=(--bridge)
  $recheck_fresh && kernel_args+=(--fresh)
  recheck_rc=0
  bash "$EX/scripts/recheck-comparator.sh" --out "$work/recheck" --bridge > "$work/recheck.comparator.out" 2>&1 || recheck_rc=1
  bash "$EX/scripts/recheck-kernel.sh" --out "$work/recheck" "${kernel_args[@]}" > "$work/recheck.kernel.out" 2>&1 || recheck_rc=1
  # Diagnostics are copied before anything below can exit: the work directory is removed on EXIT
  # and the record keeps only the last line of a failing run. Rooms are left out except their
  # shim logs (a room is a copy of the sources plus a build directory).
  if [ -n "${RECHECK_DIAG_DIR:-}" ]; then
    mkdir -p "$RECHECK_DIAG_DIR"
    cp "$work/recheck.comparator.out" "$work/recheck.kernel.out" "$RECHECK_DIAG_DIR/" 2> /dev/null || true
    find "$work/recheck" -maxdepth 1 -type f -exec cp {} "$RECHECK_DIAG_DIR/" \; 2> /dev/null || true
    [ -d "$work/recheck/configs" ] && cp -r "$work/recheck/configs" "$RECHECK_DIAG_DIR/configs" 2> /dev/null || true
    for shim_log in "$work"/recheck/rooms/*/shim.log; do
      [ -f "$shim_log" ] || continue
      cp "$shim_log" "$RECHECK_DIAG_DIR/shim.$(basename "$(dirname "$shim_log")").log" 2> /dev/null || true
    done
  fi
  if [ ! -s "$work/recheck/comparator.verdicts" ] || [ ! -s "$work/recheck/kernel.verdicts" ]; then
    cat "$work/recheck.comparator.out" "$work/recheck.kernel.out"
    echo "[FAIL] the independent recheck produced no verdicts"
    exit 1
  fi

  # recheck-record.sh renders the verdicts and writes RECHECK (complete) or RECHECK_PARTIAL
  # (otherwise); exit 0 complete pass, 1 a FAIL verdict, 2 a PARTIAL pass. Shared with
  # .github/workflows/ci-macos-recheck.yml, which runs it standalone over these same two scripts'
  # outputs.
  bash "$EX/scripts/recheck-record.sh" --work-dir "$work/recheck" --coherence-file "$work/recheck.coherence" \
    --identity "$IDENTITY" --complete-out "$RECHECK" --partial-out "$RECHECK_PARTIAL"
  record_rc=$?
  if [ "$recheck_rc" -ne 0 ] || [ "$record_rc" -eq 1 ]; then
    cat "$work/recheck.comparator.out" "$work/recheck.kernel.out" | tail -40
    exit 1
  fi
  # print_written (below) reports which of RECHECK/RECHECK_PARTIAL recheck-record.sh wrote: exit
  # 0 is a complete record (RECHECK), exit 2 a PARTIAL one (RECHECK_PARTIAL) -- exit 1 already
  # exited above.
  if [ "$record_rc" -eq 0 ]; then
    recheck_target="$RECHECK"
  else
    recheck_target="$RECHECK_PARTIAL"
  fi
fi

rust_fallback() {
  echo "  Install a Rust toolchain, or re-run through the repository's pinned dev shell"
  echo "  (flake.nix at the repository root), from the repository root:"
  if [ "$precheck_mode" != full ]; then
    # --core-only/--committed-extraction never touch charon/aeneas, so .#build (exactly what
    # --core-only needs, per flake.nix) is correct and sufficient here.
    echo "    nix develop .#build --command bash framed_channel/check.sh"
  elif $recheck; then
    # A full-gate run that reached this point already has charon/aeneas on PATH (the
    # extraction/candidate staleness stage hard-fails first otherwise); .#build lacks them, so
    # recommend the shell that actually matches what got this far.
    echo "    nix develop .#recheck --command bash framed_channel/check.sh --recheck"
  else
    echo "    nix develop .#extraction --command bash framed_channel/check.sh"
  fi
  echo "  Use --lean-only to check the Lean half alone and say so in the output."
}

# ----------------------------------------------------------------------------- cargo fmt --check

if $lean_only; then
  echo "== cargo fmt --check == [skipped: --lean-only]"
else
  echo "== cargo fmt --check =="
  if ! command -v cargo > /dev/null 2>&1; then
    echo "[FAIL] cargo is not on PATH."
    rust_fallback
    exit 2
  fi
  if ! cargo fmt --version > /dev/null 2>&1; then
    echo "[FAIL] cargo fmt is not available (rustfmt component missing)."
    rust_fallback
    exit 2
  fi
  if ! ( cd "$EX/rust" && cargo fmt --check ); then
    echo "[FAIL] cargo fmt --check"
    exit 1
  fi
  echo "[ok] cargo fmt --check"
fi

# ---------------------------------------------------------------------------------- cargo clippy

if $lean_only; then
  echo "== cargo clippy == [skipped: --lean-only]"
else
  echo "== cargo clippy =="
  if ! cargo clippy --version > /dev/null 2>&1; then
    echo "[FAIL] cargo clippy is not available (clippy component missing)."
    rust_fallback
    exit 2
  fi
  if ! ( cd "$EX/rust" && cargo clippy --all-targets -- -D warnings ); then
    echo "[FAIL] cargo clippy"
    exit 1
  fi
  echo "[ok] cargo clippy"
fi

# ------------------------------------------------------------------------------------ cargo test

if $lean_only; then
  echo "== cargo test == [skipped: --lean-only]"
else
  echo "== cargo test =="
  if ! ( cd "$EX/rust" && cargo test ); then
    echo "[FAIL] cargo test"
    exit 1
  fi
  echo "[ok] cargo test"
fi

# -------------------------------------------------------------------------- certificate identity

# Recompute the digests taken at the start: an input edited during the run fails here, before
# digests.txt names a stale identity.
echo "== certificate identity =="
now_lines="$(identity_digest_lines "$EX")" || now_lines=""
if [ "$now_lines" != "$IDENTITY_LINES" ]; then
  echo "[FAIL] the tree changed during this run: the certificate inputs no longer hash to $IDENTITY"
  diff <(printf '%s\n' "$IDENTITY_LINES") <(printf '%s\n' "$now_lines") | sed -n '1,20p'
  echo "  Re-run check.sh on a tree that is not being edited."
  exit 1
fi
{
  echo "# framed_channel source digests (generated by check.sh; do not edit)"
  echo "# The identity is the sha256 of the digest lines below, exactly as written. Recompute with:"
  echo "#   grep -vE '^(#|identity:)' certificate/digests.txt | sha256sum"
  printf '%s\n' "$IDENTITY_LINES"
  echo "identity: $IDENTITY"
} > "$DIGESTS"
if [ "$precheck_mode" != full ]; then
  echo "[ok] certificate identity unchanged during the run ($IDENTITY; nothing written under certificate/: $(precheck_flag))"
else
  echo "[ok] certificate identity unchanged during the run ($IDENTITY; written to certificate/digests.txt)"
fi

# ------------------------------------------------------------------------------------- approvals

# Last, after the generated files are written; reuses the specification stage's records.
echo "== approvals =="
print_written() {
  local f flag
  if [ "$precheck_mode" != full ]; then
    flag="$(precheck_flag)"
    echo "  (${flag#--}: nothing written under certificate/)"
    return
  fi
  for f in "$AXIOMS" "$LADDER" "$COUNTERMODELS" "$DIGESTS"; do echo "  wrote $f"; done
  if $recheck; then
    echo "  wrote ${recheck_target:-$RECHECK}"
    [ "${recheck_target:-}" = "$RECHECK_PARTIAL" ] && echo "  (PARTIAL record: certificate/recheck.txt was NOT written or changed)"
  fi
}
if $skip_approvals; then
  echo "approvals: SKIPPED (--skip-approvals; not a verification claim -- pin-bump search gate only)"
else
  approval_args=(--spec-records "$work/spec.out")
  if $bridge_ran; then approval_args+=(--aeneas); else approval_args+=(--core-only); fi
  if $require_person; then approval_args+=(--require-person); fi
  if ! bash "$EX/scripts/check-approvals.sh" "$CERT/approvals.yaml" "${approval_args[@]}"; then
    echo
    echo "check.sh: FAIL at the final stage, approvals; every earlier stage passed"
    print_written
    exit 1
  fi
fi

echo
# PASS is the verification claim, so it requires both bridge_ran (the bridge package was built and
# audited) and staleness_ran (the committed extraction was checked against charon/aeneas, not just
# trusted as-is). A core-only run ends INCOMPLETE (exit 3): every stage that ran passed, but the
# claim was not checked. A committed-extraction run likewise ends INCOMPLETE: both packages were
# built and audited, but the extraction itself was never checked. The `! $bridge_ran` and
# `! $staleness_ran` branches below are unreachable by construction once the core-only and
# committed-extraction branches have already returned, and exist so that no future edit can print
# PASS over a run that left the bridge out or never checked the extraction.
if [ "$precheck_mode" = core_only ]; then
  if $lean_only; then
    echo "check.sh: INCOMPLETE (core-only pre-check, Lean half only: every stage that ran passed; cargo fmt/clippy/test were skipped and the bridge package was not built or audited, so this is not the verification claim; run bash check.sh for the gate)"
  else
    echo "check.sh: INCOMPLETE (core-only pre-check: every stage that ran passed; the bridge package was not built or audited, so this is not the verification claim; run bash check.sh for the gate)"
  fi
  print_written
  exit 3
fi
if [ "$precheck_mode" = committed_extraction ]; then
  if $lean_only; then
    echo "check.sh: INCOMPLETE (committed-extraction check, Lean half only: every stage that ran passed; cargo fmt/clippy/test were skipped and the committed extraction is trusted as-is, NOT CHECKED, so this is not the verification claim; run full-gate.sh for the gate)"
  else
    echo "check.sh: INCOMPLETE (committed-extraction check: every stage that ran passed; the committed extraction is trusted as-is, NOT CHECKED, so this is not the verification claim; run full-gate.sh for the gate)"
  fi
  print_written
  exit 3
fi
if ! $bridge_ran; then
  echo "check.sh: INCOMPLETE (the bridge package was not built or audited in this run, so this is not the verification claim)"
  print_written
  exit 3
fi
if ! $staleness_ran; then
  echo "check.sh: INCOMPLETE (extraction staleness was not checked in this run, so this is not the verification claim)"
  print_written
  exit 3
fi
if $skip_approvals; then
  if $lean_only; then
    echo "check.sh: PASS (--skip-approvals, Lean half only: every stage but approvals passed, and cargo fmt/clippy/test were skipped; not a verification claim -- pin-bump search gate only)"
  else
    echo "check.sh: PASS (--skip-approvals: every stage but approvals passed; not a verification claim -- pin-bump search gate only)"
  fi
elif $lean_only; then
  echo "check.sh: PASS (Lean half only; cargo fmt/clippy/test were skipped)"
else
  echo "check.sh: PASS"
fi
print_written
exit 0
