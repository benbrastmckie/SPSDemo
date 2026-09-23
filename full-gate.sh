#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# full-gate.sh -- the opt-in launcher for the full Aeneas verification gate (framed_channel's
# check.sh, without --core-only or --committed-extraction).
#
# A plain `nix develop` (`.#default`) never realizes charon, aeneas, comparator or landrun, so a
# collaborator auditing proofs against the committed extraction never pays for any of them (see
# `check.sh --committed-extraction`). Running the actual gate -- rebuilding the extraction from
# charon/aeneas and proving everything against it -- is a deliberate act, this script, which:
#   1. resolves which route this machine takes, per system, from nix/aeneas-pin.json:
#        (a) the pin has a prebuilt release asset for this system -> `.#extraction` (or
#            `.#recheck` under --recheck): seconds, ~130 MB tarball + ~290 MiB of Rust nightly
#            downloads + a ~112 MB offline sysroot;
#        (b) otherwise, unless the pin marks a from-source build known broken here, offers the
#            from-source fallback `.#extraction-source` (~30 min, ~12 GiB) after a cost prompt;
#        (c) otherwise (or on decline), falls back to `check.sh --committed-extraction` in
#            `.#build`: the light in-shell audit, which prints INCOMPLETE (exit 3) and never
#            certifies. x86_64-darwin always takes this route (its nixpkgs dropped the aeneas
#            flake's platform entirely, so no from-source route exists there either).
#   2. probes the resolved shell with `nix build --dry-run` (nix/heavy-build-probe.sh) and prints
#      a warning block with the real, corrected costs before doing anything demanding;
#   3. asks `[y/N]` before every demanding step (a from-source build, the bridge's one-time ~7 GB
#      Aeneas/Mathlib fetch, a from-source Comparator/landrun build under --recheck); `--yes`
#      accepts all of them non-interactively, and a non-interactive session without `--yes` exits
#      2 rather than silently choosing yes or no;
#   4. verifies the Lean toolchain release asset against nix/lean-toolchain-pin.json
#      (nix/lean-toolchain-pin.sh, inside `.#build`) before elan can fetch it unverified: the
#      full, network check when the pinned toolchain is not yet installed under elan, or the
#      cheap, offline --check-consistency-only check when it already is (skipped entirely under
#      --support-level, which never invokes `nix` at all);
#   5. runs `check.sh` (or the committed-extraction fallback) inside the resolved shell.
#
# --recheck is honored only on the prebuilt route (`.#recheck` already bundles comparator/landrun
# alongside the prebuilt charon/aeneas): there is no shell combining `.#extraction-source` with
# comparator/landrun, so a --recheck request that lands on the source-fallback or
# committed-extraction route is dropped, with a note, rather than silently pretended to work.
#
# Usage: bash full-gate.sh [--recheck] [--source] [--yes] [--dry-run] [--support-level] [-- <check.sh args>]
#   --recheck        also run the independent recheck (see check.sh --help); needs the prebuilt
#                    route.
#   --source         force the from-source route (`.#extraction-source`) even where the pin has a
#                    prebuilt asset for this system; still asks for cost consent first (or --yes).
#                    Refused (exit 2) on x86_64-darwin, where no from-source route exists at all.
#   --yes            accept every consent prompt non-interactively.
#   --dry-run        resolve the route, print the probe and cost figures, and exit 0 without
#                    asking, fetching, building or running check.sh.
#   --support-level  resolve this system's route without running anything (no probe, no prompt,
#                    never a non-zero exit for an unsupported-for-gating system) and print
#                    `key=value` lines on stdout: system, route (prebuilt|source|
#                    committed-extraction), shell, gate (full|light-only), recheck (complete|
#                    partial|unavailable), recheck_reason, macos_fallback. This is the single
#                    machine-readable source of truth CI legs and the fresh-clone canary consume
#                    instead of each re-deriving per-OS route logic (see docs/ci.md's Platform
#                    matrix). Exits 0 always; combining it with --source/--recheck/--dry-run/--yes
#                    has no effect (it always resolves the default, non-interactive route).
#   -- ARGS...       everything after `--` is passed through to check.sh verbatim (e.g. --clean,
#                    --lean-only, --require-person-approval).
#
# Requires: bash >= 3.2 (so the stock macOS /bin/bash works; every possibly-empty array below is
# expanded in the `${arr[@]+"${arr[@]}"}` form for that reason), nix, jq.
# Exit: whatever check.sh (or its --committed-extraction fallback) exits; 2 on a usage error, a
# refused non-interactive consent, or an unsupported --source target.

if [ -z "${BASH_VERSION:-}" ]; then
  echo "full-gate.sh: run with bash >= 3.2 (bash full-gate.sh)" >&2
  exit 2
fi
case "$BASH_VERSION" in
  [0-2].*|3.[01].*)
    echo "full-gate.sh: bash >= 3.2 is required (this is bash $BASH_VERSION)" >&2
    exit 2 ;;
esac

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=nix/heavy-build-probe.sh
. "$ROOT/nix/heavy-build-probe.sh"

# bridge_deps_fetched: true when framed_channel/aeneas/'s dependencies (Aeneas, Mathlib) are
# fetched. Deliberately a local twin of the function of the same name in
# framed_channel/scripts/lib/packages.sh rather than a `source` of that file: packages.sh declares
# associative arrays (`declare -gA`, bash >= 4.2), which the stock macOS /bin/bash 3.2 this
# launcher must run under cannot parse-and-execute. Every in-shell script sources packages.sh;
# only this outside-Nix launcher cannot. tests/launcher-compat/run.sh fails if the two drift.
bridge_deps_fetched() {
  [ -d "$ROOT/framed_channel/aeneas/.lake/packages/mathlib" ] &&
    [ -d "$ROOT/framed_channel/aeneas/.lake/packages/aeneas" ]
}

# lean_pin_installed -- true when the pinned Lean toolchain (framed_channel/lean/lean-toolchain,
# identical across all three packages) is already present under elan's toolchains directory.
# elan's directory naming, confirmed against a real ~/.elan/toolchains: "owner/repo:tag" becomes
# "owner--repo---tag" (each "/" becomes "--", each ":" becomes "---").
lean_pin_installed() {
  local elan_home="${ELAN_HOME:-$HOME/.elan}" toolchain_file="$ROOT/framed_channel/lean/lean-toolchain" toolchain dirname
  [ -f "$toolchain_file" ] || return 1
  toolchain="$(tr -d '[:space:]' < "$toolchain_file")"
  [ -n "$toolchain" ] || return 1
  dirname="${toolchain//\//--}"
  dirname="${dirname//:/---}"
  [ -d "$elan_home/toolchains/$dirname" ]
}

# lean_pin_check -- verify a cache-miss Lean toolchain release asset against
# nix/lean-toolchain-pin.json before elan can fetch it unverified, run inside .#build (which
# guarantees jq; the host running full-gate.sh may not have it, even though jq is otherwise
# listed as required above -- see nix/heavy-build-probe.sh's own pin_has_asset for the same
# host-jq-may-be-absent degradation elsewhere in this file). Cheap and offline
# (--check-consistency-only) when the pinned toolchain is already installed; otherwise the full,
# network check (a real download and hash of the release asset).
lean_pin_check() {
  if lean_pin_installed; then
    nix develop "$ROOT#build" --command bash "$ROOT/nix/lean-toolchain-pin.sh" --check-consistency-only
  else
    nix develop "$ROOT#build" --command bash "$ROOT/nix/lean-toolchain-pin.sh"
  fi
}

recheck=false
force_source=false
yes=false
dry_run=false
support_level=false
check_args=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --recheck) recheck=true; shift ;;
    --source) force_source=true; shift ;;
    --yes) yes=true; shift ;;
    --dry-run) dry_run=true; shift ;;
    --support-level) support_level=true; shift ;;
    -h|--help)
      awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "${BASH_SOURCE[0]}"
      exit 0 ;;
    --) shift; check_args=(${1+"$@"}); break ;;
    *) echo "full-gate.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done

# --support-level is non-interactive and side-effect free by construction: force dry_run so the
# route-resolution chain below never calls ask(), and never let a forced --source override the
# default route it reports.
if $support_level; then
  dry_run=true
  force_source=false
fi

# Nix version floor (skipped under --support-level, which is documented to exit 0 always and
# never invokes `nix` itself -- see its own --help text above). Shared with install.sh's
# identical check via nix/nix-version-floor.sh (not a certificate-identity input).
if ! $support_level; then
  # shellcheck source=nix/nix-version-floor.sh
  . "$ROOT/nix/nix-version-floor.sh"
  nix_ver_raw="$(nix_version_string)"
  if [ -n "$nix_ver_raw" ]; then
    nix_version_floor_ok "$nix_ver_raw" "$NIX_VERSION_FLOOR"
    nix_ver_rc=$?
    if [ "$nix_ver_rc" -eq 1 ]; then
      echo "full-gate.sh: nix is older than this project's floor (needs >= $NIX_VERSION_FLOOR; found: $nix_ver_raw)." >&2
      echo "Flakes and 'nix develop'/'nix build' need at least Nix $NIX_VERSION_FLOOR. Upgrade via" >&2
      echo "  https://determinate.systems/nix-installer/ (or your package manager)." >&2
      exit 2
    elif [ "$nix_ver_rc" -eq 2 ]; then
      echo "full-gate.sh: WARNING: could not parse a version number from 'nix --version' output ('$nix_ver_raw'); continuing without the floor check" >&2
    fi
  else
    echo "full-gate.sh: WARNING: 'nix --version' produced no output; continuing without the floor check" >&2
  fi
fi

# Map uname -s/-m to a Nix system string, exactly as install.sh does, before the first `nix`
# invocation below. FULL_GATE_TEST_SYSTEM overrides this for framed_channel/tests/full-gate/run.sh
# only, so the fixture runner can exercise every {system} x {asset-availability} branch from a
# single real machine.
if [ -n "${FULL_GATE_TEST_SYSTEM:-}" ]; then
  system="$FULL_GATE_TEST_SYSTEM"
else
  case "$(uname -s)" in
    Linux) nix_os=linux ;;
    Darwin) nix_os=darwin ;;
    *) nix_os="" ;;
  esac
  case "$(uname -m)" in
    x86_64) nix_arch=x86_64 ;;
    aarch64|arm64) nix_arch=aarch64 ;;
    *) nix_arch="" ;;
  esac
  if [ -n "$nix_os" ] && [ -n "$nix_arch" ]; then
    system="${nix_arch}-${nix_os}"
  else
    system=""
  fi
fi
case "$system" in
  x86_64-linux|aarch64-linux|x86_64-darwin|aarch64-darwin) ;;
  *)
    echo "full-gate.sh: unsupported platform '$(uname -s)/$(uname -m)'" >&2
    exit 2 ;;
esac

# pin_has_asset/pin_source_known_broken read nix/aeneas-pin.json by default; FULL_GATE_TEST_PIN
# points them at a stub instead, for the fixture runner only.
pin_file="${FULL_GATE_TEST_PIN:-}"

# ask PROMPT: "[y/N] " on stdin; true on y/yes, false otherwise. A non-interactive session
# without --yes exits 2 immediately -- the consent rule applies uniformly to every demanding step.
# FULL_GATE_TEST_TTY=1 makes this treat stdin as interactive even when `[ -t 0 ]` is false, so the
# fixture runner can feed a scripted y/n reply over a pipe; real interactive use never sets it.
ask() {
  local prompt="$1" reply
  $yes && return 0
  if [ -z "${FULL_GATE_TEST_TTY:-}" ] && [ ! -t 0 ]; then
    echo "full-gate.sh: '$prompt' needs --yes in a non-interactive session (no TTY)" >&2
    exit 2
  fi
  printf '%s [y/N] ' "$prompt" >&2
  read -r reply
  case "$reply" in
    y|Y|yes|YES) return 0 ;;
    *) return 1 ;;
  esac
}

# has_aeneas_source SYSTEM: mirrors flake.nix's hasAeneasSource -- every system except
# x86_64-darwin, whose nixpkgs has dropped the aeneas flake's own platform.
has_aeneas_source() { [ "$1" != "x86_64-darwin" ]; }

# has_comparator SYSTEM: mirrors flake.nix's hasComparator list -- x86_64-linux and
# aarch64-linux only (comparator/lean-toolchain-bin are meaningful only where
# nix/lean-toolchain-bin.nix pins a release asset for this system; see flake.nix's own comment
# at its hasComparator definition). devShells.<system>.recheck exists on every system (it is
# defined unconditionally in flake.nix), but on a hasComparator-false system it drops Comparator
# and reports NOT-RUN, degrading the recheck to partial rather than failing outright.
has_comparator() { case "$1" in x86_64-linux|aarch64-linux) return 0 ;; *) return 1 ;; esac; }

# --------------------------------------------------------------------------------- route
# step: 1 prebuilt, 2 from-source (consented), 3 the committed-extraction fallback.
step=0
recheck_dropped_reason=""

if $force_source; then
  if ! has_aeneas_source "$system"; then
    echo "full-gate.sh: --source is unavailable on x86_64-darwin (no from-source aeneas route; nixpkgs there has dropped the aeneas flake's platform)" >&2
    exit 2
  fi
  cost="~30 min, ~12 GiB"
  if pin_source_known_broken "$system" "$pin_file"; then
    cost="$cost (this pin's from-source build is recorded known-broken on $system; see nix/aeneas-pin.json)"
  fi
  if $dry_run; then
    echo "full-gate.sh: --dry-run: --source would ask to build charon/aeneas from source ($cost)"
    step=2
  elif ask "Build charon/aeneas from source for $system now ($cost)?"; then
    step=2
  else
    echo "full-gate.sh: declined the --source build; nothing to fall back to (that was explicit)" >&2
    exit 0
  fi
elif pin_has_asset "$system" "$pin_file"; then
  step=1
elif ! has_aeneas_source "$system"; then
  step=3
elif pin_source_known_broken "$system" "$pin_file"; then
  $support_level || echo "note: the pin has no prebuilt asset for $system, and its from-source build is recorded known-broken here (nix/aeneas-pin.json); falling back to the committed-extraction pre-check"
  step=3
else
  cost="~30 min, ~12 GiB"
  if $dry_run; then
    $support_level || echo "full-gate.sh: --dry-run: the pin has no prebuilt asset for $system; would ask to build charon/aeneas from source ($cost)"
    step=2
  elif ask "The pin has no prebuilt asset for $system. Build charon/aeneas from source now ($cost)?"; then
    step=2
  else
    echo "note: declined the from-source build; falling back to the committed-extraction pre-check"
    step=3
  fi
fi

case "$step" in
  1) shell=$($recheck && echo recheck || echo extraction) ;;
  2)
    shell=extraction-source
    if $recheck; then
      recheck_dropped_reason="no shell combines the from-source aeneas route with comparator/landrun"
      recheck=false
    fi
    ;;
  3)
    shell=build
    if $recheck; then
      recheck_dropped_reason="the committed-extraction fallback cannot recheck an extraction it never checks"
      recheck=false
    fi
    ;;
esac
$support_level || { [ -n "$recheck_dropped_reason" ] && echo "note: --recheck dropped ($recheck_dropped_reason); running the plain gate instead"; }

if $support_level; then
  # route/gate/recheck are this system's *capability*, independent of whether this particular
  # invocation happened to pass --recheck: a CI leg or the canary reads this once, up front, to
  # decide what to run next (see docs/ci.md's Platform matrix).
  case "$step" in
    1) route=prebuilt ;;
    2) route=source ;;
    3) route=committed-extraction ;;
  esac
  if has_aeneas_source "$system"; then gate_level=full; else gate_level=light-only; fi
  recheck_reason=""
  if [ "$step" -eq 1 ] && has_comparator "$system"; then
    recheck_state=complete
  elif [ "$step" -eq 1 ]; then
    recheck_state=partial
    recheck_reason="Comparator's Landlock sandbox is Linux-only"
  elif [ "$step" -eq 2 ]; then
    recheck_state=unavailable
    recheck_reason="no shell combines the from-source aeneas route with comparator/landrun"
  else
    recheck_state=unavailable
    recheck_reason="the committed-extraction fallback cannot recheck an extraction it never checks"
  fi
  real_pin="${pin_file:-$ROOT/nix/aeneas-pin.json}"
  macos_fallback_val=false
  if command -v jq > /dev/null 2>&1 && [ -f "$real_pin" ]; then
    macos_fallback_val="$(jq -r '.macos_fallback // false' "$real_pin" 2>/dev/null || echo false)"
  fi
  echo "system=$system"
  echo "route=$route"
  echo "shell=$shell"
  echo "gate=$gate_level"
  echo "recheck=$recheck_state"
  echo "recheck_reason=$recheck_reason"
  echo "macos_fallback=$macos_fallback_val"
  exit 0
fi

# --------------------------------------------------------------------------------- probe
if ! heavy_probe "$ROOT" "devShells.${system}.${shell}"; then
  echo "full-gate.sh: the probe itself failed; see above" >&2
  exit 2
fi

echo "== full-gate.sh: resolved route =="
recheck_note=""
$recheck && recheck_note=" (--recheck)"
echo "  system: $system, shell: .#$shell$recheck_note"
if [ "$step" -eq 1 ]; then
  echo "  cost: prebuilt Aeneas route -- seconds (a ~130 MB release tarball and ~290 MiB of Rust"
  echo "        nightly downloads, both fixed-output downloads from cache.nixos.org and"
  echo "        static.rust-lang.org, plus a ~112 MB MIR sysroot built locally offline from the"
  echo "        pinned Rust nightly's vendored sources; no charon/aeneas source build)"
elif [ "$step" -eq 2 ]; then
  if $dry_run; then
    echo "  cost: from-source Aeneas build -- ~30 min, ~12 GiB"
  else
    echo "  cost: from-source Aeneas build -- ~30 min, ~12 GiB (consented above)"
  fi
fi
if [ -n "$PROBE_MINOR" ]; then
  if $dry_run; then
    echo "  also: --dry-run: would ask to build Comparator/landrun locally for --recheck now (minutes):"
    while IFS= read -r p; do echo "    $p"; done <<< "$PROBE_MINOR"
  elif ask "Build Comparator/landrun locally for --recheck now (minutes)?"; then
    echo "  also: Comparator/landrun local build(s) -- minutes:"
    while IFS= read -r p; do echo "    $p"; done <<< "$PROBE_MINOR"
  else
    shell=extraction
    if $recheck; then
      recheck_dropped_reason="declined the Comparator/landrun local build"
      recheck=false
    fi
    echo "note: --recheck dropped ($recheck_dropped_reason); running the plain gate instead"
  fi
fi
if [ -n "$PROBE_FETCH_LINE" ]; then
  echo "  $PROBE_FETCH_LINE"
fi
if [ "$PROBE_REALIZED" = false ]; then
  echo "  nothing new to realize (already warm)"
fi
if [ -n "$PROBE_SOURCE" ] && [ "$step" -ne 2 ]; then
  # Defensive: the route resolution above should make this unreachable (step 1/3 never touch a
  # from-source charon/aeneas derivation), but a probe disagreeing with the resolved route is
  # exactly the kind of drift this check exists to catch loudly rather than build through.
  echo "full-gate.sh: the probe found a from-source charon/aeneas build on the '$shell' route, which should never happen; refusing to proceed" >&2
  while IFS= read -r p; do echo "  $p" >&2; done <<< "$PROBE_SOURCE"
  exit 2
fi

# FULL_GATE_TEST_BRIDGE_FETCHED overrides bridge_deps_fetched()'s real filesystem check, for the
# fixture runner only ("1" forces fetched, "0" forces not-fetched).
bridge_fetched=false
if [ -n "${FULL_GATE_TEST_BRIDGE_FETCHED:-}" ]; then
  [ "$FULL_GATE_TEST_BRIDGE_FETCHED" = 1 ] && bridge_fetched=true
elif bridge_deps_fetched; then
  bridge_fetched=true
fi
if ! $bridge_fetched; then
  fetch_cost="~7 GB on first fetch"
  if $dry_run; then
    echo "  would also fetch: Aeneas/Mathlib bridge dependencies ($fetch_cost)"
  elif ! ask "Fetch the Aeneas/Mathlib bridge dependencies now ($fetch_cost)?"; then
    step=3
    shell=build
    if $recheck; then
      recheck_dropped_reason="the committed-extraction fallback cannot recheck an extraction it never checks"
      recheck=false
    fi
    echo "note: declined the bridge fetch; falling back to the committed-extraction pre-check"
  fi
fi

# Every route below (step 1, 2 or 3) still needs elan to have installed the pinned Lean
# toolchain, so this step's report/run is unconditional on $step, unlike the bridge fetch above.
if $dry_run; then
  if lean_pin_installed; then
    echo "  would also run: the Lean toolchain pin check (--check-consistency-only; already installed)"
  else
    echo "  would also run: the Lean toolchain pin check (downloads and hashes the release asset; not yet installed)"
  fi
fi

if $dry_run; then
  echo "full-gate.sh: --dry-run: stopping before check.sh"
  exit 0
fi

if ! lean_pin_check; then
  echo "full-gate.sh: the Lean toolchain pin check failed; see above" >&2
  exit 1
fi

# --------------------------------------------------------------------------------- run
if [ "$step" -eq 3 ]; then
  echo "== full-gate.sh: running the committed-extraction pre-check in .#build (INCOMPLETE by design) =="
  exec nix develop "$ROOT#build" --command bash "$ROOT/framed_channel/check.sh" --committed-extraction ${check_args[@]+"${check_args[@]}"}
fi

check_run_args=(${check_args[@]+"${check_args[@]}"})
$recheck && check_run_args=(--recheck ${check_run_args[@]+"${check_run_args[@]}"})
echo "== full-gate.sh: running the gate in .#$shell =="
exec nix develop "$ROOT#$shell" --command bash "$ROOT/framed_channel/check.sh" ${check_run_args[@]+"${check_run_args[@]}"}
