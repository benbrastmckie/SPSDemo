# shellcheck shell=bash disable=SC2034
# SPDX-License-Identifier: Apache-2.0
# packages.sh -- the two Lake packages and the Lean-source helpers the scripts share. SOURCED.
#
#   PACKAGE_NAMES                  core bridge, in build order
#   PKG_DIR PKG_ROOT PKG_REGISTRY PKG_NS PKG_CHALLENGE PKG_SOLUTION
#                                  per package: Lake directory, library root, registry file,
#                                  namespace its register% rows resolve in, Challenge library,
#                                  Comparator solution module
#   bridge_deps_fetched            true when aeneas/'s dependencies (Aeneas, Mathlib) are fetched
#   bridge_scope_arg PROG ARG      consumes --core-only/--aeneas into the global bridge_scope
#                                  (core|aeneas); a caller's own arg-parsing loop folds this into
#                                  its case arms (see spec-check.sh, refresh-hashes.sh)
#   bridge_enabled                 true when bridge_scope is aeneas (no inference; the caller
#                                  requires an explicit scope from its own preflight)
#   registry_rows PKG              "<name as written> <hash>" per register% row, in file order
#                                  (hash `-` when the row has none)
#   registry_hashes PKG            "<qualified name> <hash>", sorted
#   registry_names PKG             the qualified names, sorted
#   challenge_package MODULE       core or bridge; fails outside both Challenge libraries
#   challenge_file MODULE          its source path relative to framed_channel/; fails likewise
#   lean_imports FILE              the modules FILE's header imports, one per line
#   funs_external_forbidden FILE   prints and succeeds on axiom/sorry/admit/native_decide outside
#                                  comments (the hand-written trusted library models)
#   genvectors_messages FILE...    prints and succeeds on any compiler message of GenVectors.lean
#   policy_rows FILE KIND          the name of every KIND row of a certificate/policy.txt-shaped
#                                  FILE (trusted/flagged/shared-proof)
#   axiom_list LINE                the bracketed, whitespace-stripped axiom list from a "depends
#                                  on axioms: [...]" record line (not split on commas)
#   fail_each COUNTER_VAR TEMPLATE reads stdin; per non-blank line, "[FAIL] " + TEMPLATE with the
#                                  line at its one %s, and increments COUNTER_VAR
#
# The variables are for the scripts that source this file (hence SC2034 off). Paths are relative
# to the directory holding this file. Requires: bash >= 4.4, awk, perl.

_packages_ex="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

PACKAGE_NAMES=(core bridge)
declare -gA PKG_DIR=([core]=lean [bridge]=aeneas)
declare -gA PKG_ROOT=([core]=FramedChannel [bridge]=FramedChannelAeneas)
declare -gA PKG_REGISTRY=(
  [core]=lean/FramedChannel/Registry.lean
  [bridge]=aeneas/FramedChannelAeneas/Registry.lean
)
declare -gA PKG_NS=([core]=FramedChannel [bridge]=FramedChannel.Bridge)
declare -gA PKG_CHALLENGE=([core]=FramedChannelChallenge [bridge]=FramedChannelAeneasChallenge)
declare -gA PKG_SOLUTION=([core]=FramedChannel.Registry [bridge]=FramedChannelAeneas.Registry)

# Lean's warning for a declaration containing `sorry`: backticks since v4.31.0, single quotes
# before. Both match, so a toolchain bump cannot turn a sorry scan into a no-op.
LEAN_SORRY_MSG="declaration uses ['\`]sorry['\`]"

bridge_deps_fetched() {
  [ -d "$_packages_ex/aeneas/.lake/packages/mathlib" ] &&
    [ -d "$_packages_ex/aeneas/.lake/packages/aeneas" ]
}

# bridge_scope_arg PROG ARG: for ARG in --core-only/--aeneas, sets the global bridge_scope to
# core/aeneas; the caller's own arg-parsing loop calls this once per matched flag and does its
# own `shift`. Returns 1 (bridge_scope untouched) for any other ARG, so a caller can fold this
# into its case statement's flag arms without changing its own unknown-argument handling. On a
# contradiction (the scope was already set to the other value) prints "PROG: --aeneas and
# --core-only contradict each other" to stderr and returns 2; the caller exits with that status.
bridge_scope_arg() {
  local prog="$1"
  case "$2" in
    --core-only)
      if [ "${bridge_scope:-}" = aeneas ]; then
        echo "$prog: --aeneas and --core-only contradict each other" >&2
        return 2
      fi
      bridge_scope=core ;;
    --aeneas)
      if [ "${bridge_scope:-}" = core ]; then
        echo "$prog: --aeneas and --core-only contradict each other" >&2
        return 2
      fi
      bridge_scope=aeneas ;;
    *) return 1 ;;
  esac
}

# bridge_enabled: true when bridge_scope is aeneas. No inference from bridge_deps_fetched -- a
# caller using this (spec-check.sh, refresh-hashes.sh) requires an explicit scope from its own
# caller before reaching here (see their own preflight checks).
bridge_enabled() {
  [ "${bridge_scope:-}" = aeneas ]
}

registry_rows() {
  awk '
    $1 == "register%" && $2 ~ /^[A-Za-z_][A-Za-z0-9_.]*$/ {
      print $2, ((($5 == "true" || $5 == "false") && $6 ~ /^[0-9]+$/) ? $6 : "-")
    }' "$_packages_ex/${PKG_REGISTRY[$1]}"
}

registry_hashes() {
  registry_rows "$1" | awk -v ns="${PKG_NS[$1]}" '{ print ns "." $1, $2 }' | LC_ALL=C sort -u
}

registry_names() {
  registry_hashes "$1" | cut -d' ' -f1
}

challenge_package() {
  local p
  for p in "${PACKAGE_NAMES[@]}"; do
    case "$1" in
      "${PKG_CHALLENGE[$p]}"|"${PKG_CHALLENGE[$p]}".*) echo "$p"; return 0 ;;
    esac
  done
  return 1
}

challenge_file() {
  local p
  p="$(challenge_package "$1")" || return 1
  echo "${PKG_DIR[$p]}/${1//.//}.lean"
}

# The header ends at the first line that is neither an import nor blank once `--` and nested
# `/- -/` comments are removed; a docstring line that begins with "import" is inside a comment.
lean_imports() {
  awk '
    {
      line = $0; out = ""
      while (line != "") {
        o = index(line, "/-")
        if (depth > 0) {
          c = index(line, "-/")
          if (o > 0 && (c == 0 || o < c)) { depth++; line = substr(line, o + 2) }
          else if (c > 0) { depth--; line = substr(line, c + 2) }
          else { line = "" }
        } else {
          l = index(line, "--")
          if (l > 0 && (o == 0 || l < o)) { out = out substr(line, 1, l - 1); line = "" }
          else if (o > 0) { out = out substr(line, 1, o - 1); depth = 1; line = substr(line, o + 2) }
          else { out = out line; line = "" }
        }
      }
      if (out ~ /^[[:space:]]*$/) next
      if (out !~ /^[[:space:]]*import[[:space:]]/) exit
      n = split(out, w)
      for (i = 2; i <= n; i++) print w[i]
    }' "$1"
}

funs_external_forbidden() {
  perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$1" | grep -nwE 'axiom|sorry|admit|native_decide'
}

# `lake env lean --run GenVectors.lean` prints the generator's own compile messages ahead of its
# output; any such message (a warning, a sorry) is a defect of the generator, never vector data.
genvectors_messages() {
  grep -hE -e '^GenVectors\.lean:[0-9]+:[0-9]+:' -e "$LEAN_SORRY_MSG" "$@"
}

# policy_rows FILE KIND: the name of every KIND row (second field) of a certificate/policy.txt-
# shaped FILE (rows: `<kind> <name>`, KIND one of trusted/flagged/shared-proof).
policy_rows() {
  awk -v kind="$2" '$1 == kind { print $2 }' "$1"
}

# axiom_list LINE: the bracketed axiom list from one (or several newline-joined) "'<decl>'
# depends on axioms: [a, b, c]"-shaped record line, comma-separated, whitespace stripped. Does
# not split on commas -- a caller wanting individual names splits at its own call site (spaces
# are stripped globally here, so stripping before or after a `tr ',' '\n'` split is equivalent).
axiom_list() {
  sed -n 's|.*depends on axioms: \[\(.*\)\]|\1|p' <<< "$1" | tr -d ' '
}

# fail_each COUNTER_VAR TEMPLATE: for each non-blank line of stdin, print "[FAIL] " followed by
# TEMPLATE with the line substituted at its one %s (a literal % in TEMPLATE outside that
# substitution point must be escaped %%, as printf requires), and increment COUNTER_VAR (a
# variable name in the caller's scope). Collapses the "read one name per line, skip blank,
# [FAIL] a message built from it, count the failure" idiom shared by the exact-match call sites
# in check.sh and scripts/check-approvals.sh; a site whose loop body does more than that (or
# whose message already goes through its own per-domain _fail-style function such as spec_fail,
# ladder_fail or check-approvals.sh's fail) is left as its own inline loop or uses COUNTER_VAR
# directly in place of that function, as check-approvals.sh's exact-match sites do.
fail_each() {
  local -n _fail_each_counter="$1"
  local template="$2" line
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    printf '[FAIL] %s\n' "$(printf "$template" "$line")"
    _fail_each_counter=$((_fail_each_counter + 1))
  done
}
