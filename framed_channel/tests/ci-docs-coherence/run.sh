#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/ci-docs-coherence/run.sh -- fixture tests for check-ci-docs-coherence.sh.
#
# Each case builds a small --root tree under a temporary directory (a minimal docs/ci.md, two
# workflow files and one composite action satisfying every invariant, mirroring the real
# repository's structure narrowly) and checks the exit status and the file/text the output names.
# `base_tree` produces the fully-passing tree; every case starts from it and mutates one thing,
# so a negative case is a synthetic, minimal, known-cause break -- proof the check that broke it
# actually detects the break, not just that the real tree happens to be clean today.
#
# Usage: bash tests/ci-docs-coherence/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
CHECK="$EX/scripts/check-ci-docs-coherence.sh"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

failures=0
case_num=0

# base_tree DIR -- a minimal, fully-passing tree: two workflows (alpha.yml, filtered; beta.yml,
# unfiltered), one composite action, and a docs/ci.md carrying the Overview/Summary/Trigger
# policy/Cost/Timeouts sections and a Concurrency paragraph naming both workflows -- enough
# surface for all eleven invariants to find something to check.
base_tree() {
  local d="$1"
  mkdir -p "$d/.github/workflows" "$d/.github/actions/fixture-action" "$d/docs"

  cat > "$d/.github/workflows/alpha.yml" <<'EOF'
# alpha.yml -- fixture workflow, path-filtered. See docs/ci.md#cost for the rationale, and
# docs/ci.md's "Cost" section has the numbers.
name: Alpha

on:
  push:
    branches: ["main"]
    paths:
      - "src/**"
      - ".github/workflows/alpha.yml"
  pull_request:
    branches: ["main"]
    paths:
      - "src/**"
      - ".github/workflows/alpha.yml"
  workflow_dispatch:

concurrency:
  group: alpha-${{ github.ref }}
  cancel-in-progress: true

jobs:
  build:
    runs-on: ubuntu-24.04
    timeout-minutes: 10
    steps:
      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
EOF

  cat > "$d/.github/workflows/beta.yml" <<'EOF'
# beta.yml -- fixture workflow, unfiltered (whole tree). See `alpha.yml`'s `build` job for an
# example of a filtered sibling.
name: Beta

on:
  push:
    branches: ["main"]
  pull_request:
    branches: ["main"]

concurrency:
  group: beta-${{ github.ref }}
  cancel-in-progress: true

jobs:
  hygiene:
    runs-on: ubuntu-24.04
    timeout-minutes: 15
    steps:
      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
EOF

  cat > "$d/.github/actions/fixture-action/action.yml" <<'EOF'
name: fixture-action
runs:
  using: composite
  steps:
    - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
      shell: bash
EOF

  cat > "$d/docs/ci.md" <<'EOF'
# Continuous integration

Two workflows under `.github/workflows/` build and lint this fixture repository.

**Concurrency**: `alpha.yml` and `beta.yml` both key their `concurrency:` group on `github.ref`.

## Overview

Two more workflows run but carry no badge:

- [alpha.yml](../.github/workflows/alpha.yml) -- push/PR, path-filtered.
- [beta.yml](../.github/workflows/beta.yml) -- push/PR, no path filter.

## Summary

| Workflow | Trigger | What green certifies |
|---|---|---|
| [alpha.yml](../.github/workflows/alpha.yml) | push/PR to `main`, filtered | Alpha is green |
| [beta.yml](../.github/workflows/beta.yml) | push/PR to `main`, no path filter | Beta is green |

## Trigger policy

| Workflow | `paths:` | Why that is complete |
|---|---|---|
| `alpha.yml` | `src/**`, its own file | Alpha reads src/** and itself |

## Cost

Fixture cost section, referenced by the quoted-section-name tests.

## Timeouts

| Job | Timeout | Sized for |
|---|---|---|
| `alpha.yml` / `build` | 10 minutes | fixture |
| `beta.yml` / `hygiene` | 15 minutes | fixture |

## Navigation

See [Cost](#cost) above.
EOF

  cat > "$d/README.md" <<'EOF'
# Fixture repository

See [docs/ci.md's Cost section](docs/ci.md#cost) for the cost rationale.
EOF
}

run_case() {
  # run_case NAME ROOT WANT_RC WANT_TEXT
  local name="$1" root="$2" want_rc="$3" want_text="$4"
  case_num=$((case_num + 1))
  local out rc
  out="$(bash "$CHECK" --root "$root" 2>&1)"
  rc=$?
  if [ "$rc" -eq "$want_rc" ] && { [ -z "$want_text" ] || grep -qF -- "$want_text" <<< "$out"; }; then
    echo "[ok] $name (exit $rc)"
  else
    echo "[FAIL] $name: exit $rc (expected $want_rc)$( [ -n "$want_text" ] && echo ", text '$want_text' $(grep -qF -- "$want_text" <<< "$out" && echo found || echo missing)" )"
    sed 's/^/    /' <<< "$out"
    failures=$((failures + 1))
  fi
}

# 1. the fully-passing base tree
d1="$work/case1"; base_tree "$d1"
run_case "base tree: all invariants hold" "$d1" 0 "all invariants hold"

# 2. invariant 5: a SHA pin with its trailing version comment stripped
d2="$work/case2"; base_tree "$d2"
sed -i 's/@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1/@3d3c42e5aac5ba805825da76410c181273ba90b1/' \
  "$d2/.github/workflows/alpha.yml"
run_case "invariant 5: SHA pin missing its version comment" "$d2" 1 \
  ".github/workflows/alpha.yml:27: SHA-pinned uses: has no trailing '# vX.Y.Z' comment"

# 3. invariant 6: a second, different SHA for an action already pinned elsewhere
d3="$work/case3"; base_tree "$d3"
sed -i 's/actions\/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1/actions\/checkout@0000000000000000000000000000000000000000 # v1.0.0/' \
  "$d3/.github/workflows/beta.yml"
run_case "invariant 6: actions/checkout pinned to two different SHAs" "$d3" 1 \
  "invariant 6: actions/checkout pinned to 2 different SHAs"

# 4. invariant 4: a filtered workflow's push.paths omits its own file
d4="$work/case4"; base_tree "$d4"
sed -i '/- "\.github\/workflows\/alpha\.yml"/{0,/- "\.github\/workflows\/alpha\.yml"/d}' \
  "$d4/.github/workflows/alpha.yml"
run_case "invariant 4: alpha.yml's push.paths omits its own file" "$d4" 1 \
  "invariant 4: .github/workflows/alpha.yml: on.push.paths: does not list its own file"

# 5. invariant 3a: push.paths and pull_request.paths diverge
d5="$work/case5"; base_tree "$d5"
awk '
  BEGIN { n = 0 }
  /^  pull_request:/ { in_pr = 1 }
  in_pr && /"src\/\*\*"/ && n == 0 { print; print "      - \"extra/**\""; n = 1; next }
  { print }
' "$d5/.github/workflows/alpha.yml" > "$d5/.github/workflows/alpha.yml.new"
mv "$d5/.github/workflows/alpha.yml.new" "$d5/.github/workflows/alpha.yml"
run_case "invariant 3a: alpha.yml's push/pull_request paths diverge" "$d5" 1 \
  "invariant 3a: .github/workflows/alpha.yml: on.push.paths and on.pull_request.paths differ"

# 6. invariants 3a/4: a workflow_dispatch-only workflow (no push/pull_request paths: at all) is
# not reported missing -- it simply falls outside both invariants' scope.
d6="$work/case6"; base_tree "$d6"
cat > "$d6/.github/workflows/alpha.yml" <<'EOF'
# alpha.yml -- fixture workflow, dispatch-only variant (no live paths: key).
name: Alpha

on:
  workflow_dispatch:

concurrency:
  group: alpha-${{ github.ref }}
  cancel-in-progress: true

jobs:
  build:
    runs-on: ubuntu-24.04
    timeout-minutes: 10
    steps:
      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
EOF
run_case "invariants 3a/4: dispatch-only workflow is not reported missing" "$d6" 0 \
  "all invariants hold"

# 7. invariant 1: a workflow file with no docs/ci.md mention at all
d7="$work/case7"; base_tree "$d7"
cat > "$d7/.github/workflows/gamma.yml" <<'EOF'
# gamma.yml -- fixture workflow, deliberately undocumented.
name: Gamma

on:
  workflow_dispatch:

jobs:
  build:
    runs-on: ubuntu-24.04
    timeout-minutes: 10
    steps:
      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
EOF
run_case "invariant 1: gamma.yml has no docs/ci.md mention" "$d7" 1 \
  "invariant 1: gamma.yml missing from docs/ci.md's Overview Summary Timeouts section(s)"

# 8. invariant 10: the Overview's workflow-count sentence is wrong
d8="$work/case8"; base_tree "$d8"
sed -i 's/Two more workflows run but carry no badge/Three more workflows run but carry no badge/' \
  "$d8/docs/ci.md"
run_case "invariant 10: Overview's count sentence says Three, should be Two" "$d8" 1 \
  "invariant 10: Overview claims 'Three more workflows' (3) but 2 workflow file(s) minus 0 badged = 2"

# 9. invariant 2: a timeout-minutes bumped in YAML but not in docs/ci.md's Timeouts table
d9="$work/case9"; base_tree "$d9"
sed -i 's/timeout-minutes: 10/timeout-minutes: 20/' "$d9/.github/workflows/alpha.yml"
run_case "invariant 2: alpha.yml's build timeout bumped without the doc" "$d9" 1 \
  "invariant 2: .github/workflows/alpha.yml (build): timeout-minutes: 20, but docs/ci.md's Timeouts row says 10"

# 10. invariant 2: the canary's four-leg timeout_minutes matrix, one leg reordered against the doc
d10="$work/case10"; base_tree "$d10"
cat > "$d10/.github/workflows/fresh-clone-canary.yml" <<'EOF'
# fresh-clone-canary.yml -- fixture, four-leg matrix with legs 3 and 4 swapped versus the doc.
name: Fresh-clone canary

on:
  workflow_dispatch:
    inputs:
      macos:
        type: boolean
        default: false

jobs:
  canary:
    strategy:
      matrix:
        include:
          ${{ fromJSON(inputs.macos
          && '[{"os":"a","system":"x86_64-linux","timeout_minutes":120},
               {"os":"b","system":"aarch64-linux","timeout_minutes":120},
               {"os":"c","system":"x86_64-darwin","timeout_minutes":120},
               {"os":"d","system":"aarch64-darwin","timeout_minutes":105}]'
          || '[{"os":"a","system":"x86_64-linux","timeout_minutes":120}]') }}
    runs-on: ubuntu-24.04
    timeout-minutes: ${{ matrix.timeout_minutes }}
    steps:
      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
EOF
sed -i 's#| `beta.yml` / `hygiene` | 15 minutes | fixture |#| `beta.yml` / `hygiene` | 15 minutes | fixture |\n| `fresh-clone-canary.yml` | 120 / 120 / 105 / 120 minutes (x86_64-linux, aarch64-linux, aarch64-darwin, x86_64-darwin) | fixture |#' \
  "$d10/docs/ci.md"
run_case "invariant 2: canary's matrix legs 3 and 4 reordered against the doc" "$d10" 1 \
  "invariant 2: fresh-clone-canary.yml's matrix timeout_minutes (120,120,120,105) does not match docs/ci.md's Timeouts row (120,120,105,120)"

# 11. a renamed ## Timeouts heading produces [skip], not a silent pass
d11="$work/case11"; base_tree "$d11"
sed -i 's/^## Timeouts$/## Timeout Budget/' "$d11/docs/ci.md"
run_case "renamed ## Timeouts heading is [skip], not a pass" "$d11" 0 \
  "[skip] invariant 2: docs/ci.md has no '## Timeouts' heading"

# 12. invariant 3b: a YAML paths: entry with no match in the Trigger-policy row
d12="$work/case12"; base_tree "$d12"
sed -i 's#      - "src/\*\*"#      - "src/**"\n      - "docs/**"#g' "$d12/.github/workflows/alpha.yml"
run_case "invariant 3b: alpha.yml's docs/** has no Trigger-policy match" "$d12" 1 \
  "invariant 3b: .github/workflows/alpha.yml: on.paths entry 'docs/**' has no match in docs/ci.md's Trigger-policy row for alpha.yml"

# 13. invariant 3b: the brace-expansion transform's regression test -- a row using shorthand for
# the same content a naive literal comparison would false-FAIL on
d13="$work/case13"; base_tree "$d13"
sed -i 's#      - "src/\*\*"#      - "sub/x/**"\n      - "sub/y/**"#g' "$d13/.github/workflows/alpha.yml"
sed -i 's#| `alpha.yml` | `src/\*\*`, its own file | Alpha reads src/\*\* and itself |#| `alpha.yml` | `sub/{x,y}/**`, its own file | Alpha reads sub/x/** and sub/y/** and itself |#' \
  "$d13/docs/ci.md"
run_case "invariant 3b: brace shorthand sub/{x,y}/** matches both YAML entries" "$d13" 0 \
  "invariant 3b: every filtered workflow's paths: matches its Trigger-policy row"

# 14. invariant 3b: an unrecognized brace syntax (nested braces) exits 2, never a guess
d14="$work/case14"; base_tree "$d14"
sed -i 's#| `alpha.yml` | `src/\*\*`, its own file | Alpha reads src/\*\* and itself |#| `alpha.yml` | `sub/{x,{y,z}}/**`, its own file | Alpha reads a nested brace group |#' \
  "$d14/docs/ci.md"
run_case "invariant 3b: nested brace syntax exits 2, not a guess" "$d14" 2 \
  "invariant 3b: alpha.yml's Trigger-policy cell has an unrecognized brace pattern: 'sub/{x,{y,z}}/**'"

# 15. invariant 3b: a workflow_dispatch-only row (ci-macos-gate.yml's name, specifically) is
# [skip], never force-passed and never reported missing
d15="$work/case15"; base_tree "$d15"
cat > "$d15/.github/workflows/ci-macos-gate.yml" <<'EOF'
# ci-macos-gate.yml -- fixture, dispatch-only, no live paths: key.
name: CI macOS gate

on:
  workflow_dispatch:

jobs:
  aeneas-gate:
    runs-on: ubuntu-24.04
    timeout-minutes: 10
    steps:
      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
EOF
run_case "invariant 3b: ci-macos-gate.yml's row is [skip], not force-passed" "$d15" 1 \
  "[skip] invariant 3b: ci-macos-gate.yml (workflow_dispatch-only"

# 16. invariant 7: a dead anchor
d16="$work/case16"; base_tree "$d16"
sed -i 's|docs/ci\.md#cost|docs/ci.md#no-such-heading|' "$d16/README.md"
run_case "invariant 7: README.md's anchor does not resolve" "$d16" 1 \
  "invariant 7: README.md:3: docs/ci.md#no-such-heading has no matching heading"

# 17. invariant 8: a quoted nonexistent section name (the audit's "Caches" instance)
d17="$work/case17"; base_tree "$d17"
sed -i '2a # docs/ci.md'"'"'s "Caches" section has the eviction policy.' "$d17/.github/workflows/alpha.yml"
run_case "invariant 8: quoted docs/ci.md's \"Caches\" does not exist" "$d17" 1 \
  "invariant 8: .github/workflows/alpha.yml:1: docs/ci.md's \"Caches\" has no matching '## Caches' heading"

# 18. invariant 8: an unquoted reference is [skip], never FAIL
d18="$work/case18"; base_tree "$d18"
run_case "invariant 8: base tree's unquoted Cost-section mention is [skip]" "$d18" 0 \
  "[skip] invariant 8: 1 unquoted docs/ci.md's <Name> section reference(s)"

# 19. invariant 9: a job named against the wrong workflow
d19="$work/case19"; base_tree "$d19"
sed -i "s/\`alpha.yml\`'s \`build\` job/\`alpha.yml\`'s \`nonexistent\` job/" "$d19/.github/workflows/beta.yml"
run_case "invariant 9: beta.yml references alpha.yml's nonexistent job" "$d19" 1 \
  "invariant 9: .github/workflows/beta.yml:1: alpha.yml has no \`nonexistent\` job"

# 20. invariant 11: a workflow with concurrency: absent from the roster
d20="$work/case20"; base_tree "$d20"
sed -i "s/\`alpha.yml\` and \`beta.yml\` both key/\`alpha.yml\` alone keys/" "$d20/docs/ci.md"
run_case "invariant 11: beta.yml's concurrency: block is missing from the roster" "$d20" 1 \
  "invariant 11: beta.yml carries a concurrency: block but is not named in docs/ci.md's Concurrency paragraph"

# 21. invariant 12: a README.md in .github/ shadows the root README as the front page
d21="$work/case21"; base_tree "$d21"
printf '# workflows\n' > "$d21/.github/README.md"
run_case "invariant 12: .github/README.md shadows the root README" "$d21" 1 \
  "invariant 12: .github/README.md shadows the root README.md as the repository front page"

# 22. invariant 12: the lowercase spelling is caught too (GitHub resolves case-insensitively)
d22="$work/case22"; base_tree "$d22"
printf '# workflows\n' > "$d22/.github/readme.md"
run_case "invariant 12: .github/readme.md (lowercase) is caught as well" "$d22" 1 \
  "invariant 12: .github/readme.md shadows the root README.md as the repository front page"

# 23. invariant 12: a non-README map file in .github/ is not reported
d23="$work/case23"; base_tree "$d23"
printf '# workflows\n' > "$d23/.github/CONTENTS.md"
run_case "invariant 12: .github/CONTENTS.md is the sanctioned name, not a finding" "$d23" 0 \
  "invariant 12: .github/ has no README"

if [ $failures -ne 0 ]; then
  echo "tests/ci-docs-coherence: $failures of $case_num case(s) failed"
  exit 1
fi
echo "tests/ci-docs-coherence: all $case_num cases pass"
