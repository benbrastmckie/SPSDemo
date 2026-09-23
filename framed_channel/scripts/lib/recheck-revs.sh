# shellcheck shell=bash
# SPDX-License-Identifier: Apache-2.0
# recheck-revs.sh -- revision coherence of the independent recheck tools. SOURCED.
#
# The recheck is meaningful only when the recheck, core and bridge toolchains agree, the tools are
# pinned and built on the project's Lean (not Comparator's kernel Lean), the pinned lean4export is
# Comparator's parser revision, comparator is the pinned nix build, landrun enforces Landlock, the
# run is unprivileged and `systemd-run --user` works. Only the Comparator half of this is
# Linux-only (Landlock sandbox); see the "Requires" line below.
#
#   recheck_rev_coherence          one [ok]/[skip]/[FAIL] line per comparison (calls
#                                  recheck_pin_coherence first); non-zero on a mismatch. A missing
#                                  tool is a [skip], never a silent pass.
#   recheck_pin_coherence          build-free (no Comparator on PATH, no `lake build`): checks
#                                  ../../../nix/comparator-pin.json's field shapes and that
#                                  recheck/lakefile.toml's lean4export rev and
#                                  recheck/lake-manifest.json's lean4export rev both agree with
#                                  it. One [ok]/[skip]/[FAIL] line per comparison; non-zero on a
#                                  mismatch or a pin-load error.
#   recheck_tool_paths             sets RECHECK_LEAN4LEAN, RECHECK_LEAN4EXPORT (empty when not
#                                  built), RECHECK_TOOLCHAIN_BIN, RECHECK_LEANCHECKER, RECHECK_GIT,
#                                  RECHECK_COMPARATOR (real path), RECHECK_LANDRUN (empty if absent)
#   recheck_landlock_enforced      true when a write under `landrun --ro /` is denied
#   recheck_landlock_net_enforced  true when a TCP connect under `landrun --best-effort` with no
#                                  --connect-tcp grant is denied by Landlock (EACCES)
#   recheck_landlock_abi           the kernel's Landlock ABI as landrun sees it: "v<N>" when it
#                                  is below what this landrun asks for in strict mode, ">= the
#                                  ABI landrun <version> requests" otherwise
#   recheck_systemd_user_usable    true when `systemd-run --user` runs a command
#
# These four probes memoize their result in an exported RECHECK_PROBE_* variable
# (RECHECK_PROBE_LANDLOCK, _LANDLOCK_NET, _LANDLOCK_ABI, _SYSTEMD) on first call, so a later call
# in the SAME process -- or in a child process that inherits the exported variable, as
# recheck-comparator.sh and recheck-kernel.sh do when check.sh --recheck execs them after its own
# recheck_rev_coherence call already probed -- returns the cached result instead of re-probing.
# Unset (a standalone `bash recheck-comparator.sh`, ci-macos-recheck.yml, the landrun-shim
# fixture) probes fresh, exactly as before.
#   recheck_tool_revisions         the byte-stable "tool revisions" lines of recheck.txt
#   recheck_record_completeness LINES_FILE
#                                  "complete", or "PARTIAL: <n> verdict(s) NOT RUN (<list>)" for
#                                  the recheck.lines-format verdict rows in LINES_FILE (fields:
#                                  <checker> <config/package> <verdict> ...). The lean4lean-fresh
#                                  row is always present: OK/FAIL under check.sh --recheck-fresh,
#                                  NOT-RUN "not requested" otherwise -- a NOT-RUN lean4lean-fresh
#                                  row on a plain (non---recheck-fresh) run is not a partial run.
#   recheck_produced_on            "<uname -s> <uname -m> (<producer>)", producer from
#                                  ${RECHECK_PRODUCER:-local}
#
# The tools package directory is always recheck/ next to this file.
# Requires: bash >= 4.4, jq, strings (binutils), landrun, systemd-run, comparator. The kernel
# replay half (recheck-kernel.sh) needs none of landrun/systemd-run/comparator and runs on any
# platform; only the Comparator half (recheck-comparator.sh) is Linux-only (Landlock sandbox).

# The Comparator build the recheck is pinned against, the Lean kernel it runs in-process, and the
# lean4export revision its parser is built from (that Comparator revision's lake-manifest.json),
# which recheck/lakefile.toml pins too. LEAN4LEAN_REV is recheck/lakefile.toml's lean4lean pin, an
# independent HOLD pin kept as a literal here -- deliberately NOT part of the shared pin file.
#
# Single source of truth: ../../../nix/comparator-pin.json (mirrors ../../../nix/aeneas-pin.json's
# shape; ../../../nix/comparator.nix and ../../../nix/lean-toolchain-bin.nix read the same file).
# _recheck_load_pin below reads it at SOURCE TIME -- check.sh:~1516 and the verify.yml inline
# smoke block use COMPARATOR_REV/COMPARATOR_KERNEL_VERSION/COMPARATOR_KERNEL_GITHASH/
# LEAN4EXPORT_REV directly after sourcing this file, without calling a coherence function first,
# so a lazy load would leave them unset for those callers. It is non-fatal by construction (this
# file is sourced under `set -euo pipefail` in verify.yml): a missing `jq`, a missing pin file, or
# an empty/malformed field leaves the four variables empty and sets RECHECK_PIN_ERROR to a
# one-line reason, which recheck_pin_coherence (below) reports as [FAIL] rather than the load
# aborting the sourcing shell. recheck_tool_paths() matches the flake-built binary's store path
# against COMPARATOR_REV's 8-char prefix (/nix/store/*-comparator-*-<rev8>*/*).
# Sourcing guard: check.sh sources this file from two call sites (the default non---recheck path
# and the --recheck path); a caller can test this before sourcing to avoid redundant work.
_RECHECK_REVS_SOURCED=1

_recheck_revs_ex="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

# shellcheck disable=SC2034
_recheck_load_pin() {
  local pin_file="${RECHECK_PIN_FILE:-$_recheck_revs_ex/../nix/comparator-pin.json}"
  COMPARATOR_REV=""
  COMPARATOR_KERNEL_VERSION=""
  COMPARATOR_KERNEL_GITHASH=""
  LEAN4EXPORT_REV=""
  RECHECK_PIN_ERROR=""
  if ! command -v jq > /dev/null 2>&1; then
    RECHECK_PIN_ERROR="jq not on PATH"
    return 0
  fi
  if [ ! -f "$pin_file" ]; then
    RECHECK_PIN_ERROR="pin file not found: $pin_file"
    return 0
  fi
  local rev l4e_rev githash tc_version
  rev="$(jq -r '.rev // empty' "$pin_file" 2>/dev/null)" || rev=""
  l4e_rev="$(jq -r '.lean4export_rev // empty' "$pin_file" 2>/dev/null)" || l4e_rev=""
  githash="$(jq -r '.kernel_githash // empty' "$pin_file" 2>/dev/null)" || githash=""
  tc_version="$(jq -r '.lean_toolchain_version // empty' "$pin_file" 2>/dev/null)" || tc_version=""
  if [ -z "$rev" ] || [ -z "$l4e_rev" ] || [ -z "$githash" ] || [ -z "$tc_version" ]; then
    RECHECK_PIN_ERROR="malformed pin file (missing rev/lean4export_rev/kernel_githash/lean_toolchain_version): $pin_file"
    return 0
  fi
  COMPARATOR_REV="${rev:0:8}"
  COMPARATOR_KERNEL_VERSION="v${tc_version}"
  COMPARATOR_KERNEL_GITHASH="$githash"
  LEAN4EXPORT_REV="$l4e_rev"
  return 0
}
# The `|| true` puts this call in a context where bash's `set -e` is ignored for every command
# inside the function body (documented bash behavior for a function called as part of an `||`
# list), so a failing jq/read inside _recheck_load_pin can never abort a caller sourced under
# `set -euo pipefail`.
_recheck_load_pin || true

LEAN4LEAN_REV=095c0a947ab870a5dcf0797725a4caec66624285

# Sets globals for the scripts that source this file.
# shellcheck disable=SC2034
recheck_tool_paths() {
  local ex="$_recheck_revs_ex"
  local dir="$ex/recheck"
  RECHECK_LEAN4LEAN="$dir/.lake/packages/lean4lean/.lake/build/bin/lean4lean"
  RECHECK_LEAN4EXPORT="$dir/.lake/packages/lean4export/.lake/build/bin/lean4export"
  [ -x "$RECHECK_LEAN4LEAN" ] || RECHECK_LEAN4LEAN=""
  [ -x "$RECHECK_LEAN4EXPORT" ] || RECHECK_LEAN4EXPORT=""
  local prefix
  prefix="$(cd "$ex/lean" && lean --print-prefix 2>/dev/null)" || prefix=""
  RECHECK_TOOLCHAIN_BIN="${prefix:+$prefix/bin}"
  RECHECK_LEANCHECKER=""
  [ -n "$prefix" ] && [ -x "$prefix/bin/leanchecker" ] && RECHECK_LEANCHECKER="$prefix/bin/leanchecker"
  RECHECK_GIT="$(command -v git > /dev/null 2>&1 && realpath "$(command -v git)")" || RECHECK_GIT=""
  RECHECK_COMPARATOR="$(command -v comparator > /dev/null 2>&1 && readlink -f "$(command -v comparator)")" || RECHECK_COMPARATOR=""
  RECHECK_LANDRUN="$(command -v landrun 2>/dev/null)" || RECHECK_LANDRUN=""
}

# _recheck_embeds BIN HASH: true when the binary's strings contain HASH.
_recheck_embeds() {
  strings "$1" 2>/dev/null | grep -qF "$2"
}

# Comparator passes landrun --best-effort, which silently runs unsandboxed where Landlock is
# unavailable, so enforcement is probed rather than assumed. Memoized in RECHECK_PROBE_LANDLOCK
# (exported): check.sh --recheck's own recheck_rev_coherence call runs this once and the result
# is inherited by the recheck-comparator.sh/recheck-kernel.sh child processes it execs, so they
# never re-probe. A standalone caller (ci-macos-recheck.yml, the landrun-shim fixture, a bare
# `bash recheck-comparator.sh`) starts with no such variable in its environment and probes fresh,
# exactly as before.
recheck_landlock_enforced() {
  if [ -n "${RECHECK_PROBE_LANDLOCK:-}" ]; then
    [ "$RECHECK_PROBE_LANDLOCK" = 1 ]
    return
  fi
  local probe_dir rc=0
  probe_dir="$(mktemp -d)"
  if landrun --best-effort --ro / --ldd --add-exec -- "$(command -v touch)" "$probe_dir/probe" \
       > /dev/null 2>&1 || [ -e "$probe_dir/probe" ]; then
    rc=1
  fi
  rm -rf "$probe_dir"
  [ $rc -eq 0 ] && RECHECK_PROBE_LANDLOCK=1 || RECHECK_PROBE_LANDLOCK=0
  export RECHECK_PROBE_LANDLOCK
  return $rc
}

# The outer confinement of recheck-comparator.sh also runs --best-effort: landrun 0.1.17 asks for
# Landlock ABI V9 in strict mode and refuses to start on any older kernel (a hosted ubuntu-24.04
# runner is ABI v7), although every restriction the recheck relies on -- filesystem access rights
# and TCP connect/bind -- is older than that (ABI v1-v5 and v4). Best-effort silently drops what
# the kernel lacks, so "no network" is probed like "no writes" is, never assumed: with no
# --connect-tcp grant a TCP connect must fail with EACCES (Landlock's denial), not with the
# ECONNREFUSED an unconfined connect to the closed discard port gets.
recheck_landlock_net_enforced() {
  if [ -n "${RECHECK_PROBE_LANDLOCK_NET:-}" ]; then
    [ "$RECHECK_PROBE_LANDLOCK_NET" = 1 ]
    return
  fi
  local out rc=1
  out="$(landrun --best-effort --ro / --rw /dev --ldd --add-exec -- "$(command -v bash)" -c \
           'exec 3<>/dev/tcp/127.0.0.1/9' 2>&1)" || case "$out" in
    *"Permission denied"*) rc=0 ;;
  esac
  [ $rc -eq 0 ] && RECHECK_PROBE_LANDLOCK_NET=1 || RECHECK_PROBE_LANDLOCK_NET=0
  export RECHECK_PROBE_LANDLOCK_NET
  return $rc
}

# Strict mode is used here only as an ABI probe: its refusal names the kernel's ABI.
recheck_landlock_abi() {
  if [ -n "${RECHECK_PROBE_LANDLOCK_ABI:-}" ]; then
    echo "$RECHECK_PROBE_LANDLOCK_ABI"
    return
  fi
  local out result
  if out="$(landrun --ro / --ldd --add-exec -- "$(command -v true)" 2>&1)"; then
    result=">= the ABI landrun $(landrun --version 2>/dev/null | awk '{ print $NF }') requests"
  else
    out="$(printf '%s\n' "$out" | sed -n 's/.*Got Landlock ABI \(v[0-9][0-9]*\).*/\1/p' | head -1)"
    result="${out:-unknown}"
  fi
  export RECHECK_PROBE_LANDLOCK_ABI="$result"
  echo "$result"
}

recheck_systemd_user_usable() {
  if [ -n "${RECHECK_PROBE_SYSTEMD:-}" ]; then
    [ "$RECHECK_PROBE_SYSTEMD" = 1 ]
    return
  fi
  local rc=1
  command -v systemd-run > /dev/null 2>&1 &&
    systemd-run --user --wait --pipe --quiet true > /dev/null 2>&1 && rc=0
  [ $rc -eq 0 ] && RECHECK_PROBE_SYSTEMD=1 || RECHECK_PROBE_SYSTEMD=0
  export RECHECK_PROBE_SYSTEMD
  return $rc
}

# Build-free (no Comparator on PATH, no `lake build`): checks that ../../../nix/comparator-pin.json
# is well-formed and that the one hand-synced duplicate it cannot reach -- the lean4export `rev`
# literal in recheck/lakefile.toml (Lake TOML has no external-file read) -- and its generated
# recheck/lake-manifest.json both agree with it. Called first by recheck_rev_coherence, and also
# run standalone by check.sh's default (non---recheck) path, so a partial pin bump fails loudly
# without Comparator built.
recheck_pin_coherence() {
  local ex="$_recheck_revs_ex" fail=0
  local dir="$ex/recheck"
  local pin_file="${RECHECK_PIN_FILE:-$ex/../nix/comparator-pin.json}"
  local lakefile="$dir/lakefile.toml" manifest="$dir/lake-manifest.json"

  if [ -n "$RECHECK_PIN_ERROR" ]; then
    echo "[FAIL] nix/comparator-pin.json did not load: $RECHECK_PIN_ERROR"
    return 1
  fi
  if ! command -v jq > /dev/null 2>&1; then
    echo "[skip] nix/comparator-pin.json coherence (jq not on PATH)"
    return 0
  fi

  local rev l4e_rev githash tc_version src_hash l4e_hash shapes_ok=true
  rev="$(jq -r '.rev // empty' "$pin_file" 2>/dev/null)"
  l4e_rev="$(jq -r '.lean4export_rev // empty' "$pin_file" 2>/dev/null)"
  githash="$(jq -r '.kernel_githash // empty' "$pin_file" 2>/dev/null)"
  tc_version="$(jq -r '.lean_toolchain_version // empty' "$pin_file" 2>/dev/null)"
  src_hash="$(jq -r '.src_hash // empty' "$pin_file" 2>/dev/null)"
  l4e_hash="$(jq -r '.lean4export_src_hash // empty' "$pin_file" 2>/dev/null)"

  [[ "$rev" =~ ^[0-9a-f]{40}$ ]] || { echo "[FAIL] nix/comparator-pin.json .rev is not 40-hex: '${rev}'"; shapes_ok=false; }
  [[ "$l4e_rev" =~ ^[0-9a-f]{40}$ ]] || { echo "[FAIL] nix/comparator-pin.json .lean4export_rev is not 40-hex: '${l4e_rev}'"; shapes_ok=false; }
  [[ "$githash" =~ ^[0-9a-f]{40}$ ]] || { echo "[FAIL] nix/comparator-pin.json .kernel_githash is not 40-hex: '${githash}'"; shapes_ok=false; }
  [[ "$tc_version" =~ ^[0-9]+\.[0-9]+\.[0-9]+ ]] || { echo "[FAIL] nix/comparator-pin.json .lean_toolchain_version is malformed: '${tc_version}'"; shapes_ok=false; }
  [[ "$src_hash" == sha256-* ]] || { echo "[FAIL] nix/comparator-pin.json .src_hash does not start with sha256-: '${src_hash}'"; shapes_ok=false; }
  [[ "$l4e_hash" == sha256-* ]] || { echo "[FAIL] nix/comparator-pin.json .lean4export_src_hash does not start with sha256-: '${l4e_hash}'"; shapes_ok=false; }
  if $shapes_ok; then
    echo "[ok] nix/comparator-pin.json field shapes"
  else
    fail=1
  fi

  if [ ! -f "$lakefile" ]; then
    echo "[skip] recheck/lakefile.toml lean4export rev (file not found: $lakefile)"
  else
    local lakefile_l4e
    lakefile_l4e="$(awk '
      /^\[\[require\]\]/ { if (name == "lean4export") print rev; name=""; rev=""; next }
      /^name[[:space:]]*=/ { sub(/^name[[:space:]]*=[[:space:]]*"/, ""); sub(/".*/, ""); name=$0 }
      /^rev[[:space:]]*=/  { sub(/^rev[[:space:]]*=[[:space:]]*"/, "");  sub(/".*/, "");  rev=$0 }
      END { if (name == "lean4export") print rev }
    ' "$lakefile")"
    if [ -z "$lakefile_l4e" ]; then
      echo "[FAIL] could not find lean4export's rev in recheck/lakefile.toml"
      fail=1
    elif [ "$lakefile_l4e" != "$l4e_rev" ]; then
      echo "[FAIL] recheck/lakefile.toml pins lean4export '${lakefile_l4e}', not nix/comparator-pin.json's ${l4e_rev}"
      fail=1
    else
      echo "[ok] recheck/lakefile.toml pins lean4export ${lakefile_l4e:0:7} (matches nix/comparator-pin.json)"
    fi
  fi

  if [ ! -f "$manifest" ]; then
    echo "[skip] recheck/lake-manifest.json lean4export rev (file not found: $manifest)"
  else
    local manifest_l4e
    manifest_l4e="$(jq -r '.packages[] | select(.name == "lean4export") | .rev // empty' "$manifest" 2>/dev/null)"
    if [ "$manifest_l4e" != "$l4e_rev" ]; then
      echo "[FAIL] recheck/lake-manifest.json pins lean4export '${manifest_l4e}', not nix/comparator-pin.json's ${l4e_rev}"
      fail=1
    else
      echo "[ok] recheck/lake-manifest.json pins lean4export ${manifest_l4e:0:7} (matches nix/comparator-pin.json)"
    fi
  fi

  return $fail
}

recheck_rev_coherence() {
  local ex="$_recheck_revs_ex" fail=0
  local dir="$ex/recheck"
  recheck_tool_paths

  # comparator pin coherence (build-free; see recheck_pin_coherence's own header comment)
  recheck_pin_coherence || fail=1

  # toolchains
  local core_tc bridge_tc tools_tc=""
  core_tc="$(tr -d '[:space:]' < "$ex/lean/lean-toolchain")"
  bridge_tc="$(tr -d '[:space:]' < "$ex/aeneas/lean-toolchain")"
  [ -f "$dir/lean-toolchain" ] && tools_tc="$(tr -d '[:space:]' < "$dir/lean-toolchain")"
  if [ "$tools_tc" != "$core_tc" ] || [ "$bridge_tc" != "$core_tc" ]; then
    echo "[FAIL] recheck/lean-toolchain (${tools_tc:-missing}), lean/lean-toolchain ($core_tc) and aeneas/lean-toolchain ($bridge_tc) differ"
    fail=1
  else
    echo "[ok] recheck toolchain agrees ($core_tc; recheck, core and bridge)"
  fi

  # manifest revisions (lean4lean only -- lean4export is checked against nix/comparator-pin.json
  # by recheck_pin_coherence above)
  if ! command -v jq > /dev/null 2>&1; then
    echo "[skip] recheck/lake-manifest.json lean4lean revision (jq not on PATH)"
  else
    local l4l
    l4l="$(jq -r '.packages[] | select(.name == "lean4lean") | .rev // empty' "$dir/lake-manifest.json" 2>/dev/null)"
    if [ "$l4l" != "$LEAN4LEAN_REV" ]; then
      echo "[FAIL] recheck/lake-manifest.json pins lean4lean '${l4l}', not $LEAN4LEAN_REV"
      fail=1
    else
      echo "[ok] recheck/lake-manifest.json pins lean4lean ${l4l:0:7}"
    fi
  fi

  # the fetched lean4lean's toolchain (lean4export's upstream names a newer Lean; its binary check
  # below is what matters)
  local l4l_tc_file="$dir/.lake/packages/lean4lean/lean-toolchain"
  if [ ! -f "$l4l_tc_file" ]; then
    echo "[skip] fetched lean4lean toolchain (tools package not fetched; cd recheck && lake build lean4lean/lean4lean lean4export/lean4export)"
  elif [ "$(tr -d '[:space:]' < "$l4l_tc_file")" != "$core_tc" ]; then
    echo "[FAIL] the fetched lean4lean wants $(tr -d '[:space:]' < "$l4l_tc_file"), but the project is $core_tc"
    fail=1
  else
    echo "[ok] the fetched lean4lean wants $core_tc"
  fi

  # the Lean each binary was built for: the project's, and not Comparator's kernel Lean (the
  # `lake update` pitfall rewrites recheck/lean-toolchain to lean4export's)
  local githash name bin
  githash="$(cd "$ex/lean" && lean --githash 2>/dev/null)" || githash=""
  for name in lean4lean lean4export; do
    bin="$dir/.lake/packages/$name/.lake/build/bin/$name"
    if [ ! -x "$bin" ]; then
      echo "[skip] $name binary Lean revision ($name not built; cd recheck && lake build lean4lean/lean4lean lean4export/lean4export)"
    elif [ -z "$githash" ] || ! command -v strings > /dev/null 2>&1; then
      echo "[skip] $name binary Lean revision (lean --githash or strings unavailable)"
    elif ! _recheck_embeds "$bin" "$githash"; then
      echo "[FAIL] recheck/.../$name was not built by the project's Lean ($githash); rebuild after lake update --keep-toolchain"
      fail=1
    elif _recheck_embeds "$bin" "$COMPARATOR_KERNEL_GITHASH"; then
      echo "[FAIL] recheck/.../$name embeds Comparator's kernel Lean ($COMPARATOR_KERNEL_GITHASH), not only the project's"
      fail=1
    else
      echo "[ok] $name was built by the project's Lean (${githash:0:7})"
    fi
  done

  # comparator
  if [ -z "$RECHECK_COMPARATOR" ]; then
    echo "[skip] comparator revision (comparator not on PATH)"
  else
    case "$RECHECK_COMPARATOR" in
      /nix/store/*-comparator-*-"$COMPARATOR_REV"*/*)
        echo "[ok] comparator is the $COMPARATOR_REV build ($RECHECK_COMPARATOR)" ;;
      /nix/store/*-comparator-*)
        echo "[FAIL] comparator on PATH ($RECHECK_COMPARATOR) is not the $COMPARATOR_REV build"
        fail=1 ;;
      *)
        echo "[skip] comparator revision (cannot identify the revision of $RECHECK_COMPARATOR, not a nix store build)" ;;
    esac
  fi

  # landrun and Landlock enforcement
  if [ -z "$RECHECK_LANDRUN" ]; then
    echo "[skip] landrun (not on PATH)"
  elif ! recheck_landlock_enforced; then
    echo "[FAIL] landrun $(landrun --version 2>/dev/null | awk '{ print $NF }') does not enforce Landlock here: a write under --ro / succeeded"
    fail=1
  else
    echo "[ok] landrun $(landrun --version 2>/dev/null | awk '{ print $NF }') enforces Landlock (a write under --ro / was denied)"
    if ! recheck_landlock_net_enforced; then
      echo "[FAIL] landrun --best-effort does not deny network access here (kernel Landlock ABI $(recheck_landlock_abi)): a TCP connect with no --connect-tcp grant was not refused with EACCES"
      fail=1
    else
      echo "[ok] landrun --best-effort denies network access (a TCP connect with no grant got EACCES; kernel Landlock ABI $(recheck_landlock_abi))"
    fi
  fi

  # privilege and systemd-run (Comparator's upstream invocation removes AF_UNIX through it)
  if [ "$(id -u)" = 0 ]; then
    echo "[FAIL] the recheck runs as root; Comparator assumes an unprivileged user"
    fail=1
  else
    echo "[ok] unprivileged (uid $(id -u))"
  fi
  if ! command -v systemd-run > /dev/null 2>&1; then
    echo "[skip] systemd-run --user (not on PATH)"
  elif ! recheck_systemd_user_usable; then
    echo "[skip] systemd-run --user (not usable here: no user service manager)"
  else
    echo "[ok] systemd-run --user works"
  fi

  return $fail
}

# The byte-stable tool-revision lines recorded in recheck.txt (no wall times, no temporary paths).
recheck_tool_revisions() {
  local ex="$_recheck_revs_ex"
  recheck_tool_paths
  local tc
  tc="$(tr -d '[:space:]' < "$ex/lean/lean-toolchain")"
  echo "comparator: ${RECHECK_COMPARATOR:-NOT FOUND} (pinned rev $COMPARATOR_REV; in-process kernel Lean $COMPARATOR_KERNEL_VERSION, $COMPARATOR_KERNEL_GITHASH)"
  local built
  built="in recheck/"; [ -n "$RECHECK_LEAN4EXPORT" ] || built="NOT BUILT"
  echo "lean4export: $LEAN4EXPORT_REV (Comparator's parser revision), on $tc, $built"
  built="in recheck/"; [ -n "$RECHECK_LEAN4LEAN" ] || built="NOT BUILT"
  echo "lean4lean: $LEAN4LEAN_REV, on $tc, $built"
  built="present"; [ -n "$RECHECK_LEANCHECKER" ] || built="NOT FOUND"
  echo "leanchecker: the $tc toolchain's own, $built"
  if [ -n "$RECHECK_LANDRUN" ]; then
    echo "landrun: $(landrun --version 2>/dev/null | awk '{ print $NF }') ($(readlink -f "$RECHECK_LANDRUN"))"
  else
    echo "landrun: NOT FOUND"
  fi
}

# recheck_record_completeness LINES_FILE: see the header comment above.
recheck_record_completeness() {
  local file="$1" bad
  bad="$(awk '$1 != "lean4lean-fresh" && $3 == "NOT-RUN" { print $1 "/" $2 }' "$file")"
  if [ -z "$bad" ]; then
    echo complete
  else
    echo "PARTIAL: $(printf '%s\n' "$bad" | grep -c .) verdict(s) NOT RUN ($(printf '%s\n' "$bad" | LC_ALL=C sort -u | tr '\n' ',' | sed 's/,$//'))"
  fi
}

# recheck_produced_on: see the header comment above.
recheck_produced_on() {
  echo "$(uname -s) $(uname -m) (${RECHECK_PRODUCER:-local})"
}
