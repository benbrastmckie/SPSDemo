#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/aeneas-revs/run.sh -- fixture tests for aeneas_rev_coherence (scripts/lib/aeneas-revs.sh):
#   * the three `aeneas -version` shapes a bin on PATH can report -- a bare sha (from-source
#     build), `nightly-YYYY.MM.DD-<sha>` and `build-<sha>` (both release-binary shapes) -- plus a
#     mismatch;
#   * the charon comparison, which reads nix/aeneas-pin.json's `charon_rev` and never the fetched
#     checkout: no checkout at all, a STALE checkout (HEAD at an older revision carrying that
#     revision's different charon-pin -- the exact state a CI cache restored through a prefix
#     fallback once produced, which must be a [skip], never a charon [FAIL]), a fresh agreeing
#     checkout, and a fresh checkout whose charon-pin disagrees with the pin file (a genuinely
#     inconsistent pin: [FAIL]).
#
# Builds a small fixture tree under a temporary directory with its own copy of aeneas-revs.sh
# (its `ex`/`root` derivation is relative to `${BASH_SOURCE[0]}`, so the copy must live at the
# same framed_channel/scripts/lib/ depth for the paths to resolve inside the fixture), a fake
# `aeneas` on PATH reporting a version string from $FAKE_AENEAS_VERSION, optionally a fake
# `charon` reporting $FAKE_CHARON_REV, and optionally a real one-commit git repository standing in
# for aeneas/.lake/packages/aeneas.
#
# Usage: bash tests/aeneas-revs/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, jq, git.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

for tool in jq git; do
  if ! command -v "$tool" > /dev/null 2>&1; then
    echo "tests/aeneas-revs: $tool is not on PATH; run inside nix develop" >&2
    exit 2
  fi
done

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

LOCK_REV="227f4e7ac70d687a6b1a4871b3304f5a1c6994bf"
CHARON_REV="b104e24fea7d721b71e6c39fd70f26ff20bc0980"
OLD_CHARON_REV="a5591f6b94c8575a6ba2ae71090614a722f2b011"

# fixture_pin_to DIR REV -- flake.lock, lake-manifest.json and nix/aeneas-pin.json all pin REV, and
# the pin file records $CHARON_REV as its bundled charon.
fixture_pin_to() {
  local d="$1" rev="$2"
  printf '{"packages":[{"name":"aeneas","rev":"%s"}]}\n' "$rev" \
    > "$d/framed_channel/aeneas/lake-manifest.json"
  printf '{"nodes":{"aeneas":{"locked":{"rev":"%s"}}}}\n' "$rev" > "$d/flake.lock"
  printf '{"rev":"%s","charon_rev":"%s"}\n' "$rev" "$CHARON_REV" > "$d/nix/aeneas-pin.json"
}

# fixture_tree DIR -- a minimal framed_channel/ tree with agreeing toolchains and all three pinned
# places at $LOCK_REV, plus a copy of the real aeneas-revs.sh at the depth its own
# BASH_SOURCE-relative path derivation expects.
fixture_tree() {
  local d="$1"
  mkdir -p "$d/framed_channel/scripts/lib" "$d/framed_channel/lean" "$d/framed_channel/aeneas" "$d/nix"
  cp "$EX/scripts/lib/aeneas-revs.sh" "$d/framed_channel/scripts/lib/aeneas-revs.sh"
  printf 'leanprover/lean4:v4.31.0\n' > "$d/framed_channel/lean/lean-toolchain"
  printf 'leanprover/lean4:v4.31.0\n' > "$d/framed_channel/aeneas/lean-toolchain"
  fixture_pin_to "$d" "$LOCK_REV"
}

# fixture_checkout DIR CHARON_PIN -- a one-commit git repository at
# DIR/framed_channel/aeneas/.lake/packages/aeneas carrying CHARON_PIN and an agreeing
# lean-toolchain. Prints its HEAD. A commit hash cannot be chosen in advance, so a case that wants
# a FRESH checkout re-pins the tree to this HEAD afterwards (fixture_pin_to); a case that wants a
# STALE one leaves the tree pinned at $LOCK_REV.
fixture_checkout() {
  local d="$1" charon_pin="$2" co
  co="$d/framed_channel/aeneas/.lake/packages/aeneas"
  mkdir -p "$co/backends/lean"
  printf '# the charon revision this Aeneas builds against\n%s\n' "$charon_pin" > "$co/charon-pin"
  printf 'leanprover/lean4:v4.31.0\n' > "$co/backends/lean/lean-toolchain"
  git -C "$co" init -q
  git -C "$co" add charon-pin backends/lean/lean-toolchain
  git -C "$co" -c user.name=fixture -c user.email=fixture@example.invalid \
    -c commit.gpgsign=false commit -q -m fixture
  git -C "$co" rev-parse HEAD
}

failures=0
case_num=0

# run_tree NAME DIR VERSION_STRING CHARON_REV WANT_RC WANT_TEXT [REJECT_TEXT [MODE]]
#   Runs aeneas_rev_coherence in the prepared tree DIR with a fake aeneas (and, when CHARON_REV is
#   non-empty, a fake charon) on PATH. REJECT_TEXT, when non-empty, must NOT appear in the output.
#   MODE is passed to aeneas_rev_coherence as its one optional argument (--no-binaries).
run_tree() {
  local name="$1" d="$2" version="$3" charon="$4" want_rc="$5" want_text="$6" reject="${7:-}"
  local mode="${8:-}"
  case_num=$((case_num + 1))
  local bin_dir="$d/bin"
  mkdir -p "$bin_dir"
  printf '#!/usr/bin/env bash\necho "aeneas ${FAKE_AENEAS_VERSION}"\n' > "$bin_dir/aeneas"
  chmod +x "$bin_dir/aeneas"
  if [ -n "$charon" ]; then
    printf '#!/usr/bin/env bash\necho "charon 0.1.0 (${FAKE_CHARON_REV})"\n' > "$bin_dir/charon"
    chmod +x "$bin_dir/charon"
  fi

  local out rc ok=1
  out="$(
    PATH="$bin_dir:$PATH" FAKE_AENEAS_VERSION="$version" FAKE_CHARON_REV="$charon" \
      COHERENCE_MODE="$mode" bash -c '
      set -u
      # shellcheck source=/dev/null
      . "'"$d"'/framed_channel/scripts/lib/aeneas-revs.sh"
      # shellcheck disable=SC2086
      aeneas_rev_coherence $COHERENCE_MODE
    ' 2>&1
  )"
  rc=$?
  [ "$rc" -eq "$want_rc" ] || ok=0
  grep -qF -- "$want_text" <<< "$out" || ok=0
  if [ -n "$reject" ] && grep -qF -- "$reject" <<< "$out"; then ok=0; fi
  if [ "$ok" -eq 1 ]; then
    echo "[ok] $name (exit $rc)"
  else
    echo "[FAIL] $name: exit $rc (expected $want_rc), wanted '$want_text'${reject:+, must not contain '$reject'}"
    sed 's/^/    /' <<< "$out"
    failures=$((failures + 1))
  fi
}

# new_tree -- a fresh fixture tree; sets $d.
tree_num=0
new_tree() {
  tree_num=$((tree_num + 1))
  d="$work/tree$tree_num"
  fixture_tree "$d"
}

# run_case NAME VERSION_STRING WANT_RC WANT_TEXT -- the `aeneas -version` shape cases: no fetched
# checkout, and the pinned charon on PATH. (A fake charon is always supplied: the developer's own
# PATH may carry a real one, and the comparison now runs whenever charon is on PATH at all.)
run_case() {
  new_tree
  run_tree "$1" "$d" "$2" "$CHARON_REV" "$3" "$4"
}

# 1. bare full sha (a from-source build reports the plain sha; no '-' to strip)
run_case "bare full sha matches the pinned rev exactly" \
  "$LOCK_REV" 0 "[ok] aeneas on PATH is $LOCK_REV"

# 2. release-binary shape: nightly-YYYY.MM.DD-<short sha>
run_case "nightly-YYYY.MM.DD-<sha> shape, short sha is a prefix of the pinned rev" \
  "nightly-2026.09.19-227f4e7" 0 "[ok] aeneas on PATH is nightly-2026.09.19-227f4e7"

# 3. release-binary shape: build-<short sha>
run_case "build-<sha> shape, short sha is a prefix of the pinned rev" \
  "build-227f4e7" 0 "[ok] aeneas on PATH is build-227f4e7"

# 4. mismatch: a short sha that is not a prefix of the pinned rev
run_case "mismatched short sha fails" \
  "nightly-2026.09.19-abcdef1" 1 "[FAIL] aeneas on PATH reports 'nightly-2026.09.19-abcdef1', not a prefix"

# 5. no fetched checkout at all: the charon comparison still runs, against the pin file.
new_tree
run_tree "no fetched checkout: charon is still compared, against the pin file" \
  "$d" "$LOCK_REV" "$CHARON_REV" 0 "[ok] charon on PATH matches nix/aeneas-pin.json's charon_rev"

# 5b. ...and a charon that is not the pinned one fails with no checkout involved.
new_tree
run_tree "no fetched checkout: a charon that is not the pinned one fails" \
  "$d" "$LOCK_REV" "$OLD_CHARON_REV" 1 \
  "[FAIL] charon on PATH is '$OLD_CHARON_REV', but nix/aeneas-pin.json's charon_rev is $CHARON_REV"

# 6. THE CI STATE: a stale checkout (its HEAD is not the manifest revision) carrying the OLD
# charon-pin, with the correct, pinned charon on PATH. The stale-checkout [skip] is printed and
# the stale charon-pin is never read, so its revision appears nowhere in the output.
new_tree
stale_head="$(fixture_checkout "$d" "$OLD_CHARON_REV")"
run_tree "stale checkout with the old charon-pin: [skip], and the old pin is never read" \
  "$d" "$LOCK_REV" "$CHARON_REV" 0 \
  "[skip] fetched Aeneas sources are at $stale_head, manifest pins $LOCK_REV (stale checkout; lake will update it)" \
  "$OLD_CHARON_REV"

# 6b. the same stale tree: the verdict is the pin-file [ok], with no [FAIL] line at all.
run_tree "stale checkout: the charon verdict comes from the pin file, no [FAIL]" \
  "$d" "$LOCK_REV" "$CHARON_REV" 0 "[ok] charon on PATH matches nix/aeneas-pin.json's charon_rev" "[FAIL]"

# 7. fresh checkout (HEAD == the manifest revision) whose charon-pin agrees with the pin file.
new_tree
fresh_head="$(fixture_checkout "$d" "$CHARON_REV")"
fixture_pin_to "$d" "$fresh_head"
run_tree "fresh checkout agreeing with the pin file" \
  "$d" "$fresh_head" "$CHARON_REV" 0 \
  "[ok] nix/aeneas-pin.json's charon_rev matches the fetched Aeneas's charon-pin" "[FAIL]"

# 8. fresh checkout whose charon-pin DISAGREES with the pin file: a genuinely inconsistent pin.
new_tree
fresh_head="$(fixture_checkout "$d" "$OLD_CHARON_REV")"
fixture_pin_to "$d" "$fresh_head"
run_tree "fresh checkout whose charon-pin disagrees with the pin file fails" \
  "$d" "$fresh_head" "$CHARON_REV" 1 \
  "[FAIL] nix/aeneas-pin.json's charon_rev is $CHARON_REV, but Aeneas $fresh_head pins charon $OLD_CHARON_REV"

# 9. a stale checkout wanting a different Lean toolchain is not a toolchain [FAIL] either.
new_tree
fixture_checkout "$d" "$OLD_CHARON_REV" > /dev/null
printf 'leanprover/lean4:v4.30.0\n' \
  > "$d/framed_channel/aeneas/.lake/packages/aeneas/backends/lean/lean-toolchain"
run_tree "stale checkout with an older lean-toolchain: not consulted" \
  "$d" "$LOCK_REV" "$CHARON_REV" 0 "(stale checkout; lake will update it)" "[FAIL]"

# 9b. a fresh checkout wanting a different Lean toolchain IS a [FAIL].
new_tree
co="$d/framed_channel/aeneas/.lake/packages/aeneas"
fixture_checkout "$d" "$CHARON_REV" > /dev/null
printf 'leanprover/lean4:v4.30.0\n' > "$co/backends/lean/lean-toolchain"
fixture_pin_to "$d" "$(git -C "$co" rev-parse HEAD)"
run_tree "fresh checkout with a different lean-toolchain fails" \
  "$d" "$(git -C "$co" rev-parse HEAD)" "$CHARON_REV" 1 "[FAIL] the fetched Aeneas library wants"

# 10. --no-binaries (check.sh --committed-extraction): foreign charon and aeneas on PATH, both
# from another pin, are not this run's inputs -- [skip], exit 0, and never a [FAIL].
new_tree
run_tree "--no-binaries: a foreign aeneas and charon on PATH are skipped, not compared" \
  "$d" "nightly-2026.09.19-abcdef1" "$OLD_CHARON_REV" 0 \
  "[skip] charon revision (this run never invokes charon)" "[FAIL]" --no-binaries

# 10b. ...while the same tree without the flag fails on both.
run_tree "the same foreign binaries without --no-binaries fail" \
  "$d" "nightly-2026.09.19-abcdef1" "$OLD_CHARON_REV" 1 "[FAIL] charon on PATH is"

if [ $failures -ne 0 ]; then
  echo "tests/aeneas-revs: $failures of $case_num case(s) failed"
  exit 1
fi
echo "tests/aeneas-revs: all $case_num cases pass"
