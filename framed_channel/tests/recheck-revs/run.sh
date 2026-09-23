#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/recheck-revs/run.sh -- fixture tests for recheck_pin_coherence and the source-time pin
# loader _recheck_load_pin (scripts/lib/recheck-revs.sh):
#   * agreeing nix/comparator-pin.json, recheck/lakefile.toml and recheck/lake-manifest.json ->
#     all [ok];
#   * the lakefile's lean4export rev diverging from the pin -> [FAIL];
#   * the manifest's lean4export rev diverging from the pin -> [FAIL];
#   * a malformed pin file (a short rev, a missing key, invalid JSON) -> [FAIL] naming the
#     problem;
#   * the pin file absent, and jq not on PATH: sourcing recheck-revs.sh under
#     `set -euo pipefail` must survive both (the loader is non-fatal by construction), and
#     recheck_pin_coherence must report [FAIL] rather than the shell aborting;
#   * the four derived constants (COMPARATOR_REV, COMPARATOR_KERNEL_VERSION,
#     COMPARATOR_KERNEL_GITHASH, LEAN4EXPORT_REV) equal the pin's fields, with the expected
#     8-char/`v`-prefix transforms;
#   * the real repository's nix/comparator-pin.json carries no lean4lean key (LEAN4LEAN_REV is a
#     deliberately independent HOLD pin, kept out of the shared file);
#   * certificate-identity.sh's identity_digest_lines names nix/comparator-pin.json as an
#     identity input.
#
# Builds a small fixture tree under a temporary directory with its own copy of recheck-revs.sh
# (its `_recheck_revs_ex` derivation is relative to `${BASH_SOURCE[0]}`, so the copy must live at
# the same framed_channel/scripts/lib/ depth for the paths to resolve inside the fixture), plus a
# nix/comparator-pin.json, recheck/lakefile.toml and recheck/lake-manifest.json at the matching
# relative depths.
#
# Usage: bash tests/recheck-revs/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, jq, awk.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

for tool in jq awk; do
  if ! command -v "$tool" > /dev/null 2>&1; then
    echo "tests/recheck-revs: $tool is not on PATH; run inside nix develop" >&2
    exit 2
  fi
done

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
REPO_ROOT="$(cd "$EX/.." && pwd)"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

FIXTURE_REV="d03acab154d269c06e60e4de7e4cc85deebff94b"
FIXTURE_L4E_REV="076e8e57707e813375e8f9da8bf989799ace9680"
FIXTURE_GITHASH="293d5d0c0c3f3dded4688b3ccd6a33939ac5102b"
FIXTURE_TC="4.34.0"
FIXTURE_SRC_HASH="sha256-BOTlqCMjPnLTo5pJ6o5O+Pgw3QIKitdXsEBqBOhWxBc="
FIXTURE_L4E_HASH="sha256-sy3UivooYm1t1xdXu+/Fcq0x+U0V/6v19i1c/snnfFo="
OTHER_REV="0000000000000000000000000000000000000f"

# fixture_write_pin DIR REV L4E_REV GITHASH TC SRC_HASH L4E_HASH
fixture_write_pin() {
  local d="$1" rev="$2" l4e_rev="$3" githash="$4" tc="$5" src_hash="$6" l4e_hash="$7"
  cat > "$d/nix/comparator-pin.json" <<EOF
{
  "rev": "$rev",
  "src_hash": "$src_hash",
  "lean4export_rev": "$l4e_rev",
  "lean4export_src_hash": "$l4e_hash",
  "lean_toolchain_version": "$tc",
  "kernel_githash": "$githash",
  "lean_toolchain_assets": {}
}
EOF
}

# fixture_write_lakefile DIR L4E_REV -- mirrors the real recheck/lakefile.toml's two
# [[require]] blocks (lean4lean first, lean4export second), so the block-boundary parsing in
# recheck_pin_coherence is exercised the same way it is against the real file.
fixture_write_lakefile() {
  local d="$1" l4e_rev="$2"
  cat > "$d/framed_channel/recheck/lakefile.toml" <<EOF
name = "framed_channel_recheck"
license = "Apache-2.0"

[[require]]
name = "lean4lean"
git = "https://github.com/digama0/lean4lean"
rev = "095c0a947ab870a5dcf0797725a4caec66624285"

[[require]]
name = "lean4export"
git = "https://github.com/leanprover/lean4export"
rev = "$l4e_rev"
EOF
}

# fixture_write_manifest DIR L4E_REV
fixture_write_manifest() {
  local d="$1" l4e_rev="$2"
  printf '{"packages":[{"name":"lean4lean","rev":"095c0a947ab870a5dcf0797725a4caec66624285"},{"name":"lean4export","rev":"%s"}]}\n' \
    "$l4e_rev" > "$d/framed_channel/recheck/lake-manifest.json"
}

# fixture_tree DIR -- a minimal framed_channel/ tree with a copy of the real recheck-revs.sh at
# the depth its own BASH_SOURCE-relative path derivation expects, and all three pinned places
# agreeing at $FIXTURE_REV/$FIXTURE_L4E_REV.
fixture_tree() {
  local d="$1"
  mkdir -p "$d/framed_channel/scripts/lib" "$d/framed_channel/recheck" "$d/nix"
  cp "$EX/scripts/lib/recheck-revs.sh" "$d/framed_channel/scripts/lib/recheck-revs.sh"
  fixture_write_pin "$d" "$FIXTURE_REV" "$FIXTURE_L4E_REV" "$FIXTURE_GITHASH" "$FIXTURE_TC" \
    "$FIXTURE_SRC_HASH" "$FIXTURE_L4E_HASH"
  fixture_write_lakefile "$d" "$FIXTURE_L4E_REV"
  fixture_write_manifest "$d" "$FIXTURE_L4E_REV"
}

# path_without_jq -- the current $PATH with every directory that contains a `jq` executable
# removed. Used to simulate "jq not on PATH" without depending on a symlink farm covering every
# other tool this script (and recheck-revs.sh) needs.
path_without_jq() {
  local IFS=':' dir out=()
  for dir in $PATH; do
    [ -x "$dir/jq" ] && continue
    out+=("$dir")
  done
  local joined
  joined="$(IFS=:; echo "${out[*]}")"
  printf '%s' "$joined"
}

failures=0
case_num=0
tree_num=0

# new_tree -- a fresh agreeing fixture tree; sets $d.
new_tree() {
  tree_num=$((tree_num + 1))
  d="$work/tree$tree_num"
  fixture_tree "$d"
}

# run_pin NAME DIR WANT_RC WANT_TEXT [REJECT_TEXT [PATH_OVERRIDE]]
#   Sources DIR's copy of recheck-revs.sh under `set -euo pipefail` and runs
#   recheck_pin_coherence. REJECT_TEXT, when non-empty, must NOT appear in the output.
#   PATH_OVERRIDE, when non-empty, replaces $PATH for the sourcing subshell (used for the
#   jq-not-on-PATH case).
run_pin() {
  local name="$1" d="$2" want_rc="$3" want_text="$4" reject="${5:-}" path_override="${6:-}"
  case_num=$((case_num + 1))
  local out rc ok=1
  out="$(
    PATH="${path_override:-$PATH}" bash -c '
      set -euo pipefail
      # shellcheck source=/dev/null
      . "'"$d"'/framed_channel/scripts/lib/recheck-revs.sh"
      recheck_pin_coherence
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

# 1. everything agrees.
new_tree
run_pin "agreeing pin, lakefile and manifest" "$d" 0 "[ok] nix/comparator-pin.json field shapes"
run_pin "agreeing pin, lakefile and manifest (lakefile line)" "$d" 0 \
  "[ok] recheck/lakefile.toml pins lean4export ${FIXTURE_L4E_REV:0:7} (matches nix/comparator-pin.json)"
run_pin "agreeing pin, lakefile and manifest (manifest line)" "$d" 0 \
  "[ok] recheck/lake-manifest.json pins lean4export ${FIXTURE_L4E_REV:0:7} (matches nix/comparator-pin.json)"

# 2. lakefile literal diverges.
new_tree
fixture_write_lakefile "$d" "$OTHER_REV"
run_pin "lakefile lean4export literal diverges" "$d" 1 \
  "[FAIL] recheck/lakefile.toml pins lean4export '$OTHER_REV', not nix/comparator-pin.json's $FIXTURE_L4E_REV"

# 3. manifest diverges.
new_tree
fixture_write_manifest "$d" "$OTHER_REV"
run_pin "manifest lean4export rev diverges" "$d" 1 \
  "[FAIL] recheck/lake-manifest.json pins lean4export '$OTHER_REV', not nix/comparator-pin.json's $FIXTURE_L4E_REV"

# 4. malformed pin: short rev (fails the 40-hex shape check, not the loader).
new_tree
fixture_write_pin "$d" "${FIXTURE_REV:0:8}" "$FIXTURE_L4E_REV" "$FIXTURE_GITHASH" "$FIXTURE_TC" \
  "$FIXTURE_SRC_HASH" "$FIXTURE_L4E_HASH"
run_pin "malformed pin: short rev" "$d" 1 \
  "[FAIL] nix/comparator-pin.json .rev is not 40-hex: '${FIXTURE_REV:0:8}'"

# 5. malformed pin: missing key (kernel_githash absent -> the loader itself fails).
new_tree
cat > "$d/nix/comparator-pin.json" <<EOF
{
  "rev": "$FIXTURE_REV",
  "src_hash": "$FIXTURE_SRC_HASH",
  "lean4export_rev": "$FIXTURE_L4E_REV",
  "lean4export_src_hash": "$FIXTURE_L4E_HASH",
  "lean_toolchain_version": "$FIXTURE_TC"
}
EOF
run_pin "malformed pin: missing kernel_githash key" "$d" 1 \
  "[FAIL] nix/comparator-pin.json did not load: malformed pin file (missing rev/lean4export_rev/kernel_githash/lean_toolchain_version)"

# 6. malformed pin: invalid JSON.
new_tree
printf 'not valid json at all' > "$d/nix/comparator-pin.json"
run_pin "malformed pin: invalid JSON" "$d" 1 \
  "[FAIL] nix/comparator-pin.json did not load: malformed pin file (missing rev/lean4export_rev/kernel_githash/lean_toolchain_version)"

# 7. pin file absent: sourcing under set -euo pipefail survives, recheck_pin_coherence [FAIL]s.
new_tree
rm -f "$d/nix/comparator-pin.json"
run_pin "pin file absent: sourcing survives, [FAIL] not abort" "$d" 1 \
  "[FAIL] nix/comparator-pin.json did not load: pin file not found"

# 8. jq not on PATH: sourcing survives, [FAIL] rather than abort. Skipped (not failed) if this
# host happens to keep bash and jq in the same directory, since path_without_jq() would then
# strip bash itself and the case could not run at all.
new_tree
filtered_path="$(path_without_jq)"
bash_dir="$(dirname "$(command -v bash)")"
if ! printf '%s' "$filtered_path" | tr ':' '\n' | grep -qxF "$bash_dir"; then
  echo "[skip] jq-not-on-PATH case (bash and jq share a directory on this host; cannot construct a PATH with one but not the other)"
else
  run_pin "jq not on PATH: sourcing survives, [FAIL] not abort" "$d" 1 \
    "[FAIL] nix/comparator-pin.json did not load: jq not on PATH" "" "$filtered_path"
fi

# 9. derived constants equal the pin's fields (8-char prefix, v prefix, verbatim otherwise).
new_tree
case_num=$((case_num + 1))
out="$(
  bash -c '
    set -euo pipefail
    . "'"$d"'/framed_channel/scripts/lib/recheck-revs.sh"
    echo "COMPARATOR_REV=$COMPARATOR_REV"
    echo "COMPARATOR_KERNEL_VERSION=$COMPARATOR_KERNEL_VERSION"
    echo "COMPARATOR_KERNEL_GITHASH=$COMPARATOR_KERNEL_GITHASH"
    echo "LEAN4EXPORT_REV=$LEAN4EXPORT_REV"
  ' 2>&1
)"
want="COMPARATOR_REV=${FIXTURE_REV:0:8}
COMPARATOR_KERNEL_VERSION=v$FIXTURE_TC
COMPARATOR_KERNEL_GITHASH=$FIXTURE_GITHASH
LEAN4EXPORT_REV=$FIXTURE_L4E_REV"
if [ "$out" = "$want" ]; then
  echo "[ok] derived constants equal the pin's fields"
else
  echo "[FAIL] derived constants: got:"
  sed 's/^/    /' <<< "$out"
  echo "    wanted:"
  sed 's/^/    /' <<< "$want"
  failures=$((failures + 1))
fi

# 10. the real repository's pin file has no lean4lean key.
case_num=$((case_num + 1))
if jq -e '.lean4lean == null' "$REPO_ROOT/nix/comparator-pin.json" > /dev/null 2>&1; then
  echo "[ok] nix/comparator-pin.json has no lean4lean key"
else
  echo "[FAIL] nix/comparator-pin.json unexpectedly carries a lean4lean key"
  failures=$((failures + 1))
fi

# 11. certificate-identity.sh names nix/comparator-pin.json as an identity input.
case_num=$((case_num + 1))
if grep -q 'nix/comparator-pin.json' "$EX/scripts/certificate-identity.sh"; then
  echo "[ok] certificate-identity.sh's identity_digest_lines names nix/comparator-pin.json"
else
  echo "[FAIL] certificate-identity.sh does not mention nix/comparator-pin.json"
  failures=$((failures + 1))
fi

if [ $failures -ne 0 ]; then
  echo "tests/recheck-revs: $failures of $case_num case(s) failed"
  exit 1
fi
echo "tests/recheck-revs: all $case_num cases pass"
