#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# comparator-configs.sh -- derive leanprover/comparator configs from the registries and policy.txt.
#
# Per package, <pkg>.json: the Challenge library against the registry module, theorem_names the
# registered names minus the `flagged` rows, permitted_axioms the `trusted` rows. Per flagged row,
# flagged-<decl>.json (that theorem alone, the same axioms) and flagged-<decl>.expect (its native
# bv_decide helper axioms, from certificate/axioms.txt), which Comparator is expected to reject.
# Why, and what each config establishes: certificate/README.md. Byte-stable; nothing is run.
#
# Usage: bash scripts/comparator-configs.sh [--out DIR] [-h | --help]
#   --out DIR   write into DIR (created; refused under certificate/); default a fresh temporary
#               directory, whose path is printed
#
# Requires: bash >= 4.4, jq, awk. No Lean build, no network.
# Exit: 0 written, 1 an input is missing or inconsistent, 2 usage error or missing prerequisite.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CERT="$EX/certificate"
POLICY="$CERT/policy.txt"
AXIOMS="$CERT/axioms.txt"
# shellcheck source=lib/packages.sh
. "$EX/scripts/lib/packages.sh"

out=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --out)
      [ "$#" -ge 2 ] || { echo "comparator-configs.sh: --out needs a directory" >&2; exit 2; }
      out="$2"; shift 2 ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "comparator-configs.sh: unknown argument '$1' (expected --out DIR)" >&2; exit 2 ;;
  esac
done

command -v jq > /dev/null 2>&1 || { echo "comparator-configs.sh: jq is not on PATH" >&2; exit 2; }
for f in "$POLICY" "$AXIOMS"; do
  [ -f "$f" ] || { echo "comparator-configs.sh: $f is missing" >&2; exit 1; }
done

if [ -z "$out" ]; then
  out="$(mktemp -d)"
fi
# Resolved before anything is created, so a refused directory is never made.
out="$(realpath -m "$out")"
case "$out/" in
  "$(realpath -m "$CERT")"/*) echo "comparator-configs.sh: refusing to write under certificate/ ($out)" >&2; exit 2 ;;
esac
mkdir -p "$out"

json_array() { jq -R . | jq -s -c .; }

mapfile -t trusted < <(policy_rows "$POLICY" trusted)
mapfile -t flagged < <(policy_rows "$POLICY" flagged)
trusted_json="$(printf '%s\n' "${trusted[@]}" | json_array)"

write_config() {
  local file="$1" challenge="$2" solution="$3" names_json="$4" axioms_json="$5"
  jq -n --arg c "$challenge" --arg s "$solution" \
    --argjson t "$names_json" --argjson a "$axioms_json" \
    '{challenge_module: $c, solution_module: $s, theorem_names: $t, permitted_axioms: $a}' > "$file"
}

for name in "${PACKAGE_NAMES[@]}"; do
  challenge="${PKG_CHALLENGE[$name]}"
  solution="${PKG_SOLUTION[$name]}"
  registry_names "$name" > "$out/.registered.$name"
  if [ ! -s "$out/.registered.$name" ]; then
    echo "comparator-configs.sh: no register% rows in ${PKG_REGISTRY[$name]}" >&2
    exit 1
  fi
  names_json="$(grep -vxF -f <(printf '%s\n' "${flagged[@]}" "__none__") "$out/.registered.$name" |
    json_array)"
  write_config "$out/$name.json" "$challenge" "$solution" "$names_json" "$trusted_json"

  for f in "${flagged[@]}"; do
    grep -qxF "$f" "$out/.registered.$name" || continue
    record="$(grep -F "'$f' depends on axioms:" "$AXIOMS" | head -1)"
    if [ -z "$record" ]; then
      echo "comparator-configs.sh: flagged $f has no record in certificate/axioms.txt" >&2
      exit 1
    fi
    short="${f##*.}"
    prefix="${f%.*}"
    helpers="$(axiom_list "$record" | tr ',' '\n' |
      grep -E "(^|\\.)${short}\\._native\\.bv_decide\\.ax_[0-9]+_[0-9]+$" |
      sed -E "s|^(.*\\.)?(${short}\\._native)|${prefix}.\\2|" | LC_ALL=C sort -u)"
    if [ -z "$helpers" ]; then
      echo "comparator-configs.sh: flagged $f carries no native bv_decide helper axiom" >&2
      exit 1
    fi
    write_config "$out/flagged-$f.json" "$challenge" "$solution" \
      "$(printf '%s\n' "$f" | json_array)" "$trusted_json"
    printf '%s\n' $helpers > "$out/flagged-$f.expect"
  done
  rm -f "$out/.registered.$name"
done

echo "comparator-configs.sh: wrote $(cd "$out" && ls ./*.json | wc -l) config(s) to $out"
