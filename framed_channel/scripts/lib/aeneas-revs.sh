# shellcheck shell=bash
# SPDX-License-Identifier: Apache-2.0
# aeneas-revs.sh -- revision coherence of the Charon/Aeneas extraction. SOURCED.
#
# The extraction is meaningful only against the Aeneas Lean library it was generated for, so these
# four places must agree: ../nix/aeneas-pin.json's `rev`, flake.lock's aeneas revision, the aeneas
# package in aeneas/lake-manifest.json (lean/lean-toolchain = aeneas/lean-toolchain = the fetched
# library's), and `aeneas -version` on PATH (its last `-`-separated segment, a short sha, must be
# a prefix of the pinned revision -- the release binary reports its release tag, e.g.
# `nightly-YYYY.MM.DD-<short sha>`, or a from-source build reports a bare sha). `charon version` must
# equal ../nix/aeneas-pin.json's `charon_rev`.
#
# Every verdict is a function of pinned, committed inputs only. The fetched Aeneas checkout under
# aeneas/.lake/packages/aeneas is mutable state (a CI cache can restore one from an older pin; lake
# updates it on the next build), so it is consulted only when its HEAD equals the manifest's aeneas
# revision. A stale or unidentifiable checkout is a [skip] naming both revisions, never a [FAIL]:
# the same pinned inputs must give the same verdict whatever happens to be fetched. When the
# checkout IS at the manifest revision, its `charon-pin` must equal the pin file's `charon_rev`
# (a disagreement there is a genuinely inconsistent pin, which nix/bump-aeneas-pin.sh also refuses
# at bump time) and its lean-toolchain must equal ours.
#
#   aeneas_rev_coherence [--no-binaries]
#                          one [ok]/[skip]/[FAIL] line per comparison; non-zero on a mismatch. A
#                          missing tool is a [skip] with a note, never a silent pass.
#                          --no-binaries is for a run that never invokes charon or aeneas
#                          (check.sh --committed-extraction): whatever binaries of those names
#                          happen to be on PATH -- a user profile's, from another pin -- are not
#                          this run's inputs, so they are reported as [skip], not compared.
#
# Requires: bash >= 4.4, jq (else the flake.lock and pin-file comparisons skip), git (else the
# fetched checkout cannot be identified and the comparisons against it skip).

aeneas_rev_coherence() {
  local ex root fail=0 binaries=true
  [ "${1:-}" = "--no-binaries" ] && binaries=false
  ex="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
  root="$(cd "$ex/.." && pwd)"
  local lock="$root/flake.lock" manifest="$ex/aeneas/lake-manifest.json"

  # -- toolchains (core versus bridge; the fetched library's is compared further down, once the
  # checkout is known to be the pinned one)
  local core_tc bridge_tc lib_tc toolchains_ok=false
  core_tc="$(tr -d '[:space:]' < "$ex/lean/lean-toolchain")"
  bridge_tc="$(tr -d '[:space:]' < "$ex/aeneas/lean-toolchain")"
  if [ "$core_tc" != "$bridge_tc" ]; then
    echo "[FAIL] lean/lean-toolchain ($core_tc) differs from aeneas/lean-toolchain ($bridge_tc)"
    fail=1
  else
    toolchains_ok=true
    echo "[ok] toolchains agree ($core_tc; core and bridge)"
  fi

  # -- flake.lock versus lake-manifest.json versus the pin file
  local lock_rev="" manifest_rev="" aeneas_pin_file="$root/nix/aeneas-pin.json" pin_rev=""
  if ! command -v jq > /dev/null 2>&1; then
    echo "[skip] flake.lock / lake-manifest.json aeneas revisions (jq not on PATH; run inside nix develop)"
  else
    lock_rev="$(jq -r '.nodes.aeneas.locked.rev // empty' "$lock" 2>/dev/null)"
    manifest_rev="$(jq -r '.packages[] | select(.name == "aeneas") | .rev // empty' "$manifest" 2>/dev/null)"
    if [ -z "$lock_rev" ] || [ -z "$manifest_rev" ]; then
      echo "[FAIL] could not read the aeneas revision (flake.lock: '${lock_rev}', lake-manifest.json: '${manifest_rev}')"
      fail=1
    elif [ "$lock_rev" != "$manifest_rev" ]; then
      echo "[FAIL] flake.lock locks aeneas $lock_rev but aeneas/lake-manifest.json pins $manifest_rev"
      fail=1
    else
      echo "[ok] flake.lock and aeneas/lake-manifest.json both pin aeneas $lock_rev"
    fi

    if [ ! -f "$aeneas_pin_file" ]; then
      echo "[skip] nix/aeneas-pin.json rev == flake.lock aeneas rev (pin file not found)"
    else
      pin_rev="$(jq -r '.rev // empty' "$aeneas_pin_file" 2>/dev/null)"
      if [ -z "$pin_rev" ] || [ -z "$lock_rev" ]; then
        echo "[skip] nix/aeneas-pin.json rev == flake.lock aeneas rev (could not read one of the two)"
      elif [ "$pin_rev" != "$lock_rev" ]; then
        echo "[FAIL] nix/aeneas-pin.json pins aeneas $pin_rev but flake.lock locks $lock_rev -- an accidental 'nix flake update aeneas' without a pin-file update, or vice versa"
        fail=1
      else
        echo "[ok] nix/aeneas-pin.json rev == flake.lock aeneas rev ($pin_rev)"
      fi
    fi
  fi

  # -- the binary on PATH. Accepts a bare sha (a from-source build) or a release's own tag
  # (`nightly-YYYY.MM.DD-<sha>` / `build-<sha>`): only the last `-`-separated segment is compared,
  # since that is always the short sha regardless of which shape `aeneas -version` reports.
  if ! $binaries; then
    echo "[skip] aeneas binary revision (this run never invokes aeneas)"
  elif ! command -v aeneas > /dev/null 2>&1; then
    echo "[skip] aeneas binary revision (aeneas not on PATH; run inside nix develop)"
  elif [ -z "$lock_rev" ]; then
    echo "[skip] aeneas binary revision (no pinned revision to compare against)"
  else
    local bin_rev_raw bin_rev
    bin_rev_raw="$(aeneas -version 2>/dev/null | awk '{ print $2 }')"
    bin_rev="${bin_rev_raw##*-}"
    if [ -z "$bin_rev" ] || [ "${lock_rev#"$bin_rev"}" = "$lock_rev" ]; then
      echo "[FAIL] aeneas on PATH reports '${bin_rev_raw}', not a prefix of the pinned $lock_rev"
      fail=1
    else
      echo "[ok] aeneas on PATH is $bin_rev_raw (short sha $bin_rev is a prefix of the pinned revision)"
    fi
  fi

  # -- the fetched Aeneas checkout: fresh (HEAD == the manifest revision), stale, or absent
  local checkout="$ex/aeneas/.lake/packages/aeneas" checkout_head="" checkout_state=absent
  if [ -d "$checkout" ]; then
    checkout_state=unknown
    if command -v git > /dev/null 2>&1; then
      checkout_head="$(git -C "$checkout" rev-parse HEAD 2>/dev/null || true)"
    fi
    if [ -n "$checkout_head" ] && [ -n "$manifest_rev" ]; then
      if [ "$checkout_head" = "$manifest_rev" ]; then checkout_state=fresh; else checkout_state=stale; fi
    fi
  fi
  case "$checkout_state" in
    absent) echo "[skip] fetched Aeneas sources (not fetched; nothing to compare against)" ;;
    unknown) echo "[skip] fetched Aeneas sources (could not read the checkout's HEAD or the manifest revision, so it is not consulted)" ;;
    stale) echo "[skip] fetched Aeneas sources are at $checkout_head, manifest pins $manifest_rev (stale checkout; lake will update it)" ;;
    fresh) echo "[ok] fetched Aeneas sources are at the manifest revision ($checkout_head)" ;;
  esac

  if [ "$checkout_state" = fresh ] && $toolchains_ok; then
    local lib_file="$checkout/backends/lean/lean-toolchain"
    if [ -f "$lib_file" ]; then
      lib_tc="$(tr -d '[:space:]' < "$lib_file")"
      if [ "$lib_tc" != "$core_tc" ]; then
        echo "[FAIL] the fetched Aeneas library wants $lib_tc, but lean/lean-toolchain is $core_tc"
        fail=1
      else
        echo "[ok] the fetched Aeneas library's toolchain agrees ($lib_tc)"
      fi
    fi
  fi

  # -- charon against the pin file's charon_rev: pinned inputs only, no dependence on .lake
  local pin_charon="" charon_rev=""
  if [ -f "$aeneas_pin_file" ] && command -v jq > /dev/null 2>&1; then
    pin_charon="$(jq -r '.charon_rev // empty' "$aeneas_pin_file" 2>/dev/null)"
  fi
  if ! $binaries; then
    echo "[skip] charon revision (this run never invokes charon)"
  elif ! command -v charon > /dev/null 2>&1; then
    echo "[skip] charon revision (charon not on PATH; run inside nix develop)"
  elif [ -z "$pin_charon" ]; then
    echo "[skip] charon revision (nix/aeneas-pin.json's charon_rev is unreadable; jq not on PATH, or no pin file)"
  else
    charon_rev="$(charon version 2>/dev/null | sed -n 's/.*(\([0-9a-f]*\)).*/\1/p')"
    if [ -z "$charon_rev" ] || [ "$charon_rev" != "$pin_charon" ]; then
      echo "[FAIL] charon on PATH is '${charon_rev}', but nix/aeneas-pin.json's charon_rev is $pin_charon"
      fail=1
    else
      echo "[ok] charon on PATH matches nix/aeneas-pin.json's charon_rev (${pin_charon:0:7})"
    fi
  fi

  # -- the pin file's charon_rev against the fetched checkout's own charon-pin (fresh checkout only)
  if [ "$checkout_state" = fresh ] && [ -n "$pin_charon" ] && [ -f "$checkout/charon-pin" ]; then
    local upstream_pin
    upstream_pin="$(grep -vE '^[[:space:]]*(#|$)' "$checkout/charon-pin" | head -1 | tr -d '[:space:]')"
    if [ "$upstream_pin" != "$pin_charon" ]; then
      echo "[FAIL] nix/aeneas-pin.json's charon_rev is $pin_charon, but Aeneas $checkout_head pins charon $upstream_pin in its charon-pin -- an inconsistent pin; re-run nix/bump-aeneas-pin.sh"
      fail=1
    else
      echo "[ok] nix/aeneas-pin.json's charon_rev matches the fetched Aeneas's charon-pin (${upstream_pin:0:7})"
    fi
  fi

  return $fail
}
