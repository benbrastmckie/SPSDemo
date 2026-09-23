#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# certificate-identity.sh -- the content identity the generated certificate files name.
#
# The identity is the sha256 of the digest lines of certificate/digests.txt: sha256sum over the
# inputs of a check.sh run (sources, build definitions, pins, policy, candidates, vectors and these
# scripts), never over a generated file, an approval or a manifest. Scope and rationale:
# certificate/README.md. Recompute by hand, from framed_channel/:
#   grep -vE '^(#|identity:)' certificate/digests.txt | sha256sum
#
# rust/Cargo.toml and rust/Cargo.lock are hashed through a version-normalized view rather than raw
# bytes: cargo_version_normalized_sha256 (scripts/lib/approval-digests.sh, the single shared
# definition also used by source_sha256) excludes only the root package's own `version` field --
# dependency versions, the lockfile format version (`version = 4`), `edition`, `rust-version` and
# every other field are still hashed verbatim, unnormalized. Every other listed input is still
# hashed as raw bytes.
#
# Sourced:
#   identity_file_list [DIR]      the digested paths, relative to DIR, sorted
#   identity_digest_lines [DIR]   digest lines over that list (rust/Cargo.toml and rust/Cargo.lock
#                                  via cargo_version_normalized_sha256, everything else via plain
#                                  sha256sum), then ../flake.nix, ../flake.lock,
#                                  ../rust-toolchain.toml, ../nix/comparator.nix,
#                                  ../nix/comparator-pin.json, ../nix/lean-toolchain-bin.nix,
#                                  ../nix/landrun.nix, ../nix/aeneas-pin.json,
#                                  ../nix/aeneas-prebuilt.nix, ../nix/mir-sysroot.nix
#   identity_of_lines             the identity (hex) of digest lines on stdin
#
# Executed: bash scripts/certificate-identity.sh [--check] [-h | --help]
#   (no option)  print the tree's identity (sha256:<hex>)
#   --check      compare the tree's identity with digests.txt (whose own lines must hash to it),
#                axioms.txt, ladder.txt, countermodels.txt and, when present, recheck.txt; and
#                fail an axioms.txt that carries a NOT AUDITED package section (written by a run
#                that left a package out, which is not the verification claim)
#
# Requires: bash >= 4.4, coreutils (sha256sum), find.
# Exit: 0 printed or every file names this tree, 1 a mismatch, a NOT AUDITED section or a
# missing input, 2 usage error.

_certificate_identity_ex="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/approval-digests.sh
. "$_certificate_identity_ex/scripts/lib/approval-digests.sh"

identity_file_list() {
  local dir="${1:-$_certificate_identity_ex}"
  ( cd "$dir" && {
      find rust -path rust/target -prune -o -type f \
        \( -name '*.rs' -o -name Cargo.toml -o -name Cargo.lock -o -name rustfmt.toml \) -print
      find lean/FramedChannel lean/FramedChannelChallenge aeneas/FramedChannelAeneas \
        aeneas/FramedChannelAeneasChallenge -type f -name '*.lean'
      printf '%s\n' aeneas/GenVectors.lean lean/FramedChannelChallenge.lean \
        aeneas/FramedChannelAeneasChallenge.lean lean/lakefile.toml lean/lean-toolchain \
        lean/lake-manifest.json \
        aeneas/lakefile.toml aeneas/lean-toolchain aeneas/lake-manifest.json \
        certificate/vectors.txt certificate/policy.txt \
        certificate/candidates.txt \
        check.sh scripts/refresh-hashes.sh scripts/refresh-vectors.sh scripts/refresh-extraction.sh \
        scripts/lib/aeneas-revs.sh scripts/spec-check.sh scripts/refresh-candidates.sh \
        scripts/lib/approval-digests.sh scripts/check-approvals.sh approve.sh \
        scripts/comparator-configs.sh scripts/certificate-identity.sh scripts/check-spdx.sh \
        scripts/lib/packages.sh \
        recheck/lakefile.toml recheck/lean-toolchain recheck/lake-manifest.json \
        scripts/lib/recheck-revs.sh \
        recheck/landrun-shim.sh scripts/recheck-comparator.sh scripts/recheck-kernel.sh \
        scripts/recheck-record.sh
    } | LC_ALL=C sort )
}

identity_digest_lines() {
  local dir="${1:-$_certificate_identity_ex}"
  ( cd "$dir" || exit 1
    root="$(cargo_root_package_name rust/Cargo.toml 2> /dev/null)" || root=""
    identity_file_list "$dir" | while IFS= read -r f; do
      case "$f" in
        rust/Cargo.toml) cargo_version_normalized_sha256 "$f" || exit 1 ;;
        rust/Cargo.lock) cargo_version_normalized_sha256 "$f" "$root" || exit 1 ;;
        *) sha256sum "$f" || exit 1 ;;
      esac
    done || exit 1
    for f in ../flake.nix ../flake.lock ../rust-toolchain.toml \
             ../nix/comparator.nix ../nix/comparator-pin.json ../nix/lean-toolchain-bin.nix \
             ../nix/landrun.nix \
             ../nix/aeneas-pin.json ../nix/aeneas-prebuilt.nix ../nix/mir-sysroot.nix; do
      [ -f "$f" ] && sha256sum "$f"
    done
    exit 0 )
}

identity_of_lines() {
  sha256sum | cut -d' ' -f1
}

# The identity recorded in a generated file: the `identity:` line of digests.txt, or the
# `certificate identity:` line (optionally a `# ` comment) of every other generated file.
_identity_recorded_in() {
  sed -n -E 's/^(# )?(certificate )?identity: sha256:([0-9a-f]{64})$/\3/p' "$1" | head -1
}

_identity_check() {
  local ex="$_certificate_identity_ex" cert="$_certificate_identity_ex/certificate"
  local lines tree fail=0 f rec
  if ! lines="$(identity_digest_lines "$ex")"; then
    echo "[FAIL] could not digest the certificate inputs (a listed file is missing)"
    return 1
  fi
  tree="$(printf '%s\n' "$lines" | identity_of_lines)"
  echo "tree identity: sha256:$tree"

  if [ ! -f "$cert/digests.txt" ]; then
    echo "[FAIL] certificate/digests.txt is missing"
    fail=1
  else
    rec="$(_identity_recorded_in "$cert/digests.txt")"
    local own
    own="$(grep -vE '^(#|identity:)' "$cert/digests.txt" | identity_of_lines)"
    if [ -z "$rec" ]; then
      echo "[FAIL] certificate/digests.txt has no identity: line"
      fail=1
    elif [ "$own" != "$rec" ]; then
      echo "[FAIL] certificate/digests.txt: its digest lines hash to sha256:$own, but its identity: line says sha256:$rec"
      fail=1
    elif [ "$rec" != "$tree" ]; then
      echo "[FAIL] certificate/digests.txt is for identity sha256:$rec, but the tree is sha256:$tree (not regenerated for this tree)"
      diff <(grep -vE '^(#|identity:)' "$cert/digests.txt") <(printf '%s\n' "$lines") | sed -n '1,20p' | sed 's/^/       /'
      fail=1
    else
      echo "[ok] certificate/digests.txt names this tree (and its digest lines hash to its identity)"
    fi
  fi

  for f in axioms.txt ladder.txt countermodels.txt recheck.txt; do
    if [ ! -f "$cert/$f" ]; then
      if [ "$f" = recheck.txt ]; then
        echo "[skip] certificate/recheck.txt is absent (independent recheck NOT RUN; see check.sh --recheck)"
      else
        echo "[FAIL] certificate/$f is missing"
        fail=1
      fi
      continue
    fi
    rec="$(_identity_recorded_in "$cert/$f")"
    if [ -z "$rec" ]; then
      echo "[FAIL] certificate/$f records no certificate identity"
      fail=1
    elif [ "$f" = axioms.txt ] && grep -q 'NOT AUDITED' "$cert/$f"; then
      # A current check.sh --core-only writes nothing here; a file like this came from a run that
      # left a package out, and naming this tree's identity does not make it the claim.
      echo "[FAIL] certificate/axioms.txt carries a NOT AUDITED package section: it was written by a run that did not audit every package, so it is not the verification claim (regenerate with a full check.sh run)"
      fail=1
    elif [ "$rec" != "$tree" ]; then
      if [ "$f" = recheck.txt ]; then
        echo "[FAIL] certificate/recheck.txt is for identity sha256:$rec, but the tree is sha256:$tree (STALE; rerun check.sh --recheck)"
      else
        echo "[FAIL] certificate/$f is for identity sha256:$rec, but the tree is sha256:$tree"
      fi
      fail=1
    elif [ "$f" = recheck.txt ] && ! grep -qx 'record: complete' "$cert/$f"; then
      # Defense in depth against a hand-copied or mis-adopted partial record: a committed
      # recheck.txt that names this tree's identity but is not a complete record (every verdict
      # NOT-RUN outside the optional lean4lean-fresh line accounted for) is never a pass.
      echo "[FAIL] certificate/recheck.txt names this tree but is not a complete record ($(sed -n 's/^record: //p' "$cert/$f" | head -1)): a partial record may never be the committed recheck.txt"
      fail=1
    else
      echo "[ok] certificate/$f names this tree"
    fi
  done
  return $fail
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  set -u
  case "${1:-}" in
    --check) _identity_check; exit $? ;;
    "")
      lines="$(identity_digest_lines)" || { echo "certificate-identity.sh: a listed file is missing" >&2; exit 1; }
      echo "sha256:$(printf '%s\n' "$lines" | identity_of_lines)"
      ;;
    -h|--help)
      awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "${BASH_SOURCE[0]}"
      exit 0 ;;
    *) echo "certificate-identity.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
fi
