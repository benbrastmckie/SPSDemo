#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# certificate-freshness.sh -- did a gate run leave certificate/ as it is committed?
#
# A gate run (check.sh --aeneas, full-gate.sh --yes) rewrites the generated files under
# framed_channel/certificate/. Fresh means the run wrote what is already committed, so an edit to a
# digested input that was not followed by a regeneration shows up here as a diff.
#
# The committed certificate is the one the x86_64-linux gate writes. Exactly one token of it
# depends on the host: the target triple on axioms.txt's `lean:` line, which is `lean --version`
# verbatim (x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu, arm64-apple-darwin...). On any
# other host a byte-for-byte comparison can therefore never pass. --portable-host blanks that one
# token on both sides before comparing; the Lean version, the Lean commit and every other byte
# must still match, so a green portable run on another architecture also shows that the rest of
# the certificate is reproduced there byte-for-byte.
#
# Usage: bash scripts/certificate-freshness.sh [--portable-host] [--repo DIR] [-h | --help]
#   (no option)      strict: any difference from the index fails (the x86_64-linux gate)
#   --portable-host  ignore the target triple on axioms.txt's `lean:` line (every other host)
#   --repo DIR       the git work tree to inspect (default: the one holding this script)
#
# Compares the work tree with the index, like `git diff`; untracked files are not considered.
# Requires: bash, git, sed, diff.
# Exit: 0 fresh, 1 stale, 2 usage error or not a git work tree.

set -u

portable=false
repo=""
while [ $# -gt 0 ]; do
  case "$1" in
    --portable-host) portable=true ;;
    --repo)
      [ $# -ge 2 ] || { echo "certificate-freshness.sh: --repo needs a directory" >&2; exit 2; }
      repo="$2"; shift ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "certificate-freshness.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
  shift
done

if [ -z "$repo" ]; then
  repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
fi
if ! git -C "$repo" rev-parse --is-inside-work-tree > /dev/null 2>&1; then
  echo "certificate-freshness.sh: '$repo' is not a git work tree" >&2
  exit 2
fi
repo="$(git -C "$repo" rev-parse --show-toplevel)"
cert="framed_channel/certificate"

# The one host-dependent token: the second field of `lean: Lean (version V, TRIPLE, commit C, ...`.
# A line of any other shape is left alone, which makes the comparison strict again: fail-safe.
blank_triple() {
  sed -E 's/^(lean: Lean \(version [^,]+, )[^,]+(, commit [0-9a-f]+, )/\1<target-triple>\2/'
}

changed="$(git -C "$repo" diff --name-only -- "$cert")"
if [ -z "$changed" ]; then
  echo "[ok] certificate fresh: the gate wrote what is committed under $cert"
  exit 0
fi

if ! $portable; then
  git -C "$repo" --no-pager diff -- "$cert"
  echo "[FAIL] stale certificate file(s): $(echo "$changed" | tr '\n' ' ')" >&2
  exit 1
fi

stale=""
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if [ "$f" = "$cert/axioms.txt" ] && [ -f "$repo/$f" ]; then
    git -C "$repo" show ":$f" | blank_triple > "$tmp/committed"
    blank_triple < "$repo/$f" > "$tmp/written"
    if diff -u "$tmp/committed" "$tmp/written" > "$tmp/diff"; then
      echo "[ok] $f differs from the committed file only in the target triple of its lean: line:"
      echo "       committed: $(git -C "$repo" show ":$f" | sed -n 's/^lean: //p' | head -1)"
      echo "       this host: $(sed -n 's/^lean: //p' "$repo/$f" | head -1)"
      continue
    fi
    sed "s|^--- .*|--- committed $f (target triple blanked)|; s|^+++ .*|+++ written $f (target triple blanked)|" "$tmp/diff"
  else
    git -C "$repo" --no-pager diff -- "$f"
  fi
  stale="$stale $f"
done <<< "$changed"

if [ -n "$stale" ]; then
  echo "[FAIL] stale certificate file(s):$stale" >&2
  exit 1
fi
echo "[ok] certificate fresh up to the host's target triple"
exit 0
