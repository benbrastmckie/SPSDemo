#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# refresh-vectors.sh -- regenerate certificate/vectors.txt by evaluating the Aeneas extraction.
#
# aeneas/GenVectors.lean evaluates the extraction of rust/src and prints (input, output) records;
# rust/tests/differential.rs compares the compiled Rust against them. Run after regenerating the
# extraction and re-read the diff: every changed record is a translated behaviour that changed.
# This is the only writer of the file; check.sh's differential vectors stage regenerates into a
# temporary file and diffs, so the gate never repairs what it guards.
#
# Usage: bash scripts/refresh-vectors.sh [-h | --help]
#
# Requires: bash >= 4.4, the pinned Lean toolchain and aeneas/'s dependencies (Aeneas and Mathlib,
# about 7 GB, network on first fetch). The generator runs interpreted (lake env lean --run).
# Exit: 0 written or current, 1 the build or the generator failed, 2 usage error.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/packages.sh
. "$EX/scripts/lib/packages.sh"
CERT="$EX/certificate"
VECTORS="$CERT/vectors.txt"

case "${1:-}" in
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
esac
if [ "$#" -gt 0 ]; then
  echo "refresh-vectors.sh: unexpected argument '$1' (try --help)" >&2
  echo "  to report drift without writing, run: bash check.sh" >&2
  exit 2
fi

mkdir -p "$CERT"

tmp="$(mktemp)"
err="$(mktemp)"
trap 'rm -f "$tmp" "$err"' EXIT

# The generator imports the generated extraction only; build exactly that before evaluating.
if ! ( cd "$EX/aeneas" && lake build FramedChannelAeneas.Extracted.Funs ) > "$err" 2>&1; then
  echo "refresh-vectors.sh: could not build the extraction (aeneas/FramedChannelAeneas.Extracted.Funs)" >&2
  tail -20 "$err" >&2
  exit 1
fi

if ! ( cd "$EX/aeneas" && lake env lean --run GenVectors.lean ) > "$tmp" 2> "$err"; then
  echo "refresh-vectors.sh: could not run aeneas/GenVectors.lean" >&2
  cat "$tmp" "$err" | tail -20 >&2
  exit 1
fi

if genvectors_messages "$tmp" "$err" >&2; then
  echo "refresh-vectors.sh: aeneas/GenVectors.lean emitted compiler messages (above); fix them first" >&2
  exit 1
fi

if [ ! -s "$tmp" ]; then
  echo "refresh-vectors.sh: the generator produced no output" >&2
  exit 1
fi

changed=1
if [ -f "$VECTORS" ] && cmp -s "$tmp" "$VECTORS"; then
  changed=0
fi

cp "$tmp" "$VECTORS"
if [ $changed -eq 1 ]; then
  echo "refresh-vectors.sh: rewrote certificate/vectors.txt"
else
  echo "refresh-vectors.sh: certificate/vectors.txt already current (no change)"
fi
exit 0
