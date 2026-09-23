#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# refresh-extraction.sh -- regenerate the Charon/Aeneas extraction of the framed_channel crate.
#
# Writes aeneas/FramedChannelAeneas/Extracted/{Types,Funs}.lean from one whole-crate
# `charon cargo --preset=aeneas` run (per-module runs would duplicate shared declarations). Run it
# after any rust/src edit and re-read the diff. It never writes the hand-written FunsExternal.lean:
# it checks that the `rust_fun` names Aeneas's FunsExternal_Template.lean needs equal those
# FunsExternal.lean defines, and that FunsExternal.lean declares no axiom, sorry, admit or
# native_decide. Details and remedies: aeneas/README.md.
#
# Usage: bash scripts/refresh-extraction.sh [--dest DIR] [--no-coherence] [--llbc-out FILE] [-h | --help]
#   --dest DIR        write Types.lean and Funs.lean into DIR, leaving the committed files untouched
#   --no-coherence    skip the revision-coherence check (check.sh runs it as its own stage)
#   --llbc-out FILE   also copy the charon LLBC to FILE (check.sh reuses it for the candidates)
#
# Requires: bash >= 4.4, perl, charon and aeneas at the revisions pinned in ../flake.lock
# (nix develop .#extraction, or bash full-gate.sh), jq for the coherence check.
# Exit: 0 written or current, 1 extraction failed or the externals disagree, 2 usage error or
# missing prerequisite.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="$EX/aeneas/FramedChannelAeneas/Extracted"
SUBDIR="FramedChannelAeneas/Extracted"
EXTERNAL="$OUT/FunsExternal.lean"
# shellcheck source=lib/packages.sh
. "$EX/scripts/lib/packages.sh"

dest=""
llbc_out=""
coherence=true
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dest)
      [ "$#" -ge 2 ] || { echo "refresh-extraction.sh: --dest needs a directory" >&2; exit 2; }
      dest="$2"; shift 2 ;;
    --no-coherence) coherence=false; shift ;;
    --llbc-out)
      [ "$#" -ge 2 ] || { echo "refresh-extraction.sh: --llbc-out needs a file" >&2; exit 2; }
      llbc_out="$2"; shift 2 ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "refresh-extraction.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done

for tool in charon aeneas; do
  if ! command -v "$tool" > /dev/null 2>&1; then
    echo "refresh-extraction.sh: $tool is not on PATH." >&2
    echo "  From the repository root: nix develop .#extraction --command bash framed_channel/scripts/refresh-extraction.sh (or bash full-gate.sh)" >&2
    exit 2
  fi
done

if $coherence; then
  # shellcheck source=lib/aeneas-revs.sh
  . "$EX/scripts/lib/aeneas-revs.sh"
  if ! aeneas_rev_coherence; then
    echo "refresh-extraction.sh: revision coherence failed; not extracting" >&2
    exit 1
  fi
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# A private target directory, so the LLBC never depends on incremental state in rust/target.
if ! ( cd "$EX/rust" && CARGO_TARGET_DIR="$work/target" \
       charon cargo --preset=aeneas --dest-file "$work/framed_channel.llbc" ) \
       > "$work/charon.log" 2>&1; then
  echo "refresh-extraction.sh: charon failed" >&2
  cat "$work/charon.log" >&2
  exit 1
fi

if [ -n "$llbc_out" ] && ! cp "$work/framed_channel.llbc" "$llbc_out"; then
  echo "refresh-extraction.sh: could not copy the LLBC to $llbc_out" >&2
  exit 1
fi

if ! aeneas -backend lean -split-files -all-computable -subdir "$SUBDIR" -dest "$work/out" \
       -no-progress-bar "$work/framed_channel.llbc" > "$work/aeneas.log" 2>&1; then
  echo "refresh-extraction.sh: aeneas failed" >&2
  cat "$work/aeneas.log" >&2
  exit 1
fi

gen="$work/out/$SUBDIR"
# Exactly the two generated files plus the external-function template. A
# `TypesExternal_Template.lean` (an unmodelled external type) or any other extra file fails.
produced="$(cd "$gen" && find . -type f | sed 's|^\./||' | LC_ALL=C sort | tr '\n' ' ')"
if [ "$produced" != "Funs.lean FunsExternal_Template.lean Types.lean " ]; then
  echo "refresh-extraction.sh: unexpected output set: $produced" >&2
  echo "  (expected Funs.lean FunsExternal_Template.lean Types.lean)" >&2
  exit 1
fi
# The generated files themselves must declare no axiom. The template is all axioms by
# construction and is never scanned or written.
if grep -nE '^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]' \
     "$gen/Types.lean" "$gen/Funs.lean"; then
  echo "refresh-extraction.sh: the extraction declares an axiom; refusing to write it" >&2
  exit 1
fi

# The `rust_fun "..."` names of a Lean file, one per line, sorted. Attributes may span lines, so
# the file is joined into one line first; whitespace inside a name is squeezed.
rust_fun_names() {
  tr '\n' ' ' < "$1" | grep -o 'rust_fun[[:space:]]*"[^"]*"' \
    | sed 's/^rust_fun[[:space:]]*"//; s/"$//; s/[[:space:]]\{1,\}/ /g' | LC_ALL=C sort -u
}

if [ ! -f "$EXTERNAL" ]; then
  echo "refresh-extraction.sh: aeneas/$SUBDIR/FunsExternal.lean is missing." >&2
  echo "  Funs.lean imports it; it must define (never axiomatize) these externals:" >&2
  rust_fun_names "$gen/FunsExternal_Template.lean" | sed 's/^/    /' >&2
  exit 1
fi
rust_fun_names "$gen/FunsExternal_Template.lean" > "$work/names.template"
rust_fun_names "$EXTERNAL" > "$work/names.defined"
if ! cmp -s "$work/names.template" "$work/names.defined"; then
  echo "refresh-extraction.sh: the externals Aeneas needs differ from those FunsExternal.lean defines" >&2
  echo "  needed by the extraction (template):" >&2
  sed 's/^/    /' "$work/names.template" >&2
  echo "  defined in aeneas/$SUBDIR/FunsExternal.lean:" >&2
  sed 's/^/    /' "$work/names.defined" >&2
  echo "  Remedy: resolve a new external by an idiomatic Rust rewrite, a definition with a proved" >&2
  echo "  spec, or a refactor (never an axiom); delete a definition the library now provides." >&2
  exit 1
fi

# The hand-written models must be definitions (comments may name the forbidden words).
if funs_external_forbidden "$EXTERNAL"; then
  echo "refresh-extraction.sh: aeneas/$SUBDIR/FunsExternal.lean uses axiom, sorry, admit or" >&2
  echo "  native_decide; its models must be proved definitions" >&2
  exit 1
fi

target="${dest:-$OUT}"
mkdir -p "$target"
changed=false
for f in Types.lean Funs.lean; do
  if ! cmp -s "$gen/$f" "$target/$f"; then
    cp "$gen/$f" "$target/$f"
    changed=true
  fi
done

if [ -n "$dest" ]; then
  echo "refresh-extraction.sh: wrote Types.lean and Funs.lean to $dest"
elif $changed; then
  echo "refresh-extraction.sh: rewrote Types.lean and Funs.lean in aeneas/$SUBDIR/ (re-read the diff before committing)"
else
  echo "refresh-extraction.sh: Types.lean and Funs.lean in aeneas/$SUBDIR/ are already current"
fi
