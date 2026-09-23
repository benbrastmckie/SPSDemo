#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# recheck-comparator.sh -- run leanprover/comparator on the example, in fresh clean rooms.
#
# One fresh room per config (comparator-configs.sh): core, each flagged-<decl>, and with --bridge
# the bridge. Each room is populated from the certificate's digested file list (its digests must
# equal the source tree's) and runs, once,
#   systemd-run --user --property=RestrictAddressFamilies=~AF_UNIX ... \
#     landrun --best-effort <outer confinement: writes only in the room and /dev, no network> -- \
#     lake env comparator <config>
# with COMPARATOR_LANDRUN=recheck/landrun-shim.sh. The bridge room links the source tree's fetched
# packages read-only; a before/after snapshot of them must not change. How Comparator's six
# assumptions are met, and what a verdict establishes: certificate/README.md.
#
# Verdicts (fail closed):
#   core, bridge  OK                  exit 0, kernel accepts, last line "Your solution is okay!"
#   flagged-*     EXPECTED-REJECTION  non-zero exit, last line "uncaught exception: Illegal axiom
#                                     detected: '<helper>'" for a helper in flagged-<decl>.expect
#   any           FAIL                anything else, including a flagged pass
#   any           NOT-RUN             a tool or build is absent, or no --bridge; with a reason
#
# Usage: bash scripts/recheck-comparator.sh --out DIR [--bridge] [-h | --help]
#   --out DIR      working directory (created): rooms, logs, DIR/comparator.verdicts
#                  (`<config> <verdict> <seconds> <note>`) and DIR/comparator.deviations
#   --bridge       also run the bridge room (needs aeneas/.lake/packages fetched)
#
# Requires: bash >= 4.4, jq. On Linux, also: comparator, landrun, systemd-run --user, the built
# recheck/ tools (recheck-revs.sh) -- a missing one makes every verdict NOT-RUN. On any other
# platform every verdict is NOT-RUN with reason "Landlock sandbox is Linux-only" (Comparator's
# sandbox needs Landlock; the portable kernel-replay half is scripts/recheck-kernel.sh).
# Exit: 0 no verdict FAIL, 1 a verdict FAIL, 2 usage error.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out=""
bridge=false
while [ "$#" -gt 0 ]; do
  case "$1" in
    --out) [ "$#" -ge 2 ] || { echo "recheck-comparator.sh: --out needs a directory" >&2; exit 2; }; out="$2"; shift 2 ;;
    --bridge) bridge=true; shift ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "recheck-comparator.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done
[ -n "$out" ] || { echo "recheck-comparator.sh: --out DIR is required" >&2; exit 2; }
mkdir -p "$out"
out="$(cd "$out" && pwd)"

# shellcheck source=lib/recheck-revs.sh
. "$EX/scripts/lib/recheck-revs.sh"
# shellcheck source=certificate-identity.sh
. "$EX/scripts/certificate-identity.sh"
# shellcheck source=lib/packages.sh
. "$EX/scripts/lib/packages.sh"
recheck_tool_paths

VERDICTS="$out/comparator.verdicts"
DEVIATIONS="$out/comparator.deviations"
: > "$VERDICTS"
: > "$DEVIATIONS"
SHIM="$EX/recheck/landrun-shim.sh"
failures=0

verdict() {
  # verdict CONFIG VERDICT SECONDS NOTE
  printf '%s %s %s %s\n' "$1" "$2" "$3" "$4" >> "$VERDICTS"
  [ "$2" = FAIL ] && failures=$((failures + 1))
  return 0
}

# finish: the bridge line when --bridge was not given, the verdicts, and the exit status.
finish() {
  $bridge || verdict bridge NOT-RUN 0 "bridge package stage skipped"
  cat "$VERDICTS"
  [ "$failures" -eq 0 ] && exit 0
  exit 1
}

# ------------------------------------------------------------------ configs
if ! command -v jq > /dev/null 2>&1; then
  verdict core NOT-RUN 0 "jq not on PATH"
  $bridge && verdict bridge NOT-RUN 0 "jq not on PATH"
  finish
fi
if ! bash "$EX/scripts/comparator-configs.sh" --out "$out/configs" > "$out/configs.log" 2>&1; then
  echo "recheck-comparator.sh: comparator-configs.sh failed" >&2
  cat "$out/configs.log" >&2
  verdict core FAIL 0 "comparator-configs.sh could not derive the configs"
  finish
fi
configs=(core)
for f in "$out"/configs/flagged-*.json; do
  [ -e "$f" ] || continue
  configs+=("$(basename "$f" .json)")
done
$bridge && configs+=(bridge)

# ------------------------------------------------------------------------ platform
# Comparator's sandbox is landrun/Landlock, which is Linux-only. On any other platform, every
# config is NOT-RUN with this reason -- never a refusal of the whole recheck (the portable kernel
# replay, scripts/recheck-kernel.sh, still runs).
if [ "$(uname -s)" != Linux ]; then
  for c in "${configs[@]}"; do verdict "$c" NOT-RUN 0 "Landlock sandbox is Linux-only"; done
  finish
fi

# ------------------------------------------------------------------ preconditions
missing=""
[ -n "$RECHECK_COMPARATOR" ] || missing="comparator not on PATH"
[ -z "$missing" ] && [ -z "$RECHECK_LANDRUN" ] && missing="landrun not on PATH"
[ -z "$missing" ] && [ -z "$RECHECK_LEAN4EXPORT" ] && missing="lean4export not built (cd recheck && lake build lean4lean/lean4lean lean4export/lean4export)"
[ -z "$missing" ] && [ -z "$RECHECK_TOOLCHAIN_BIN" ] && missing="the pinned Lean toolchain is not installed"
[ -z "$missing" ] && [ -z "$RECHECK_GIT" ] && missing="git not on PATH"
[ -z "$missing" ] && ! recheck_systemd_user_usable && missing="systemd-run --user not usable"
if [ -n "$missing" ]; then
  for c in "${configs[@]}"; do verdict "$c" NOT-RUN 0 "$missing"; done
  finish
fi
if [ "$(id -u)" = 0 ]; then
  for c in "${configs[@]}"; do verdict "$c" FAIL 0 "running as root (Comparator assumes an unprivileged user)"; done
  finish
fi
if ! recheck_landlock_enforced; then
  for c in "${configs[@]}"; do verdict "$c" FAIL 0 "landrun does not enforce Landlock here (a write under --ro / succeeded)"; done
  finish
fi
if ! recheck_landlock_net_enforced; then
  for c in "${configs[@]}"; do verdict "$c" FAIL 0 "landrun --best-effort does not deny network access here (a TCP connect with no grant was not refused with EACCES; kernel Landlock ABI $(recheck_landlock_abi))"; done
  finish
fi

toolchain_prefix="$(dirname "$RECHECK_TOOLCHAIN_BIN")"
git_dir="$(dirname "$RECHECK_GIT")"

# Which file `lake` is depends on the elan that installed the toolchain. Upstream's elan leaves
# the release's ELF binary in place; nixpkgs' elan (the dev shell's, so every hosted runner's)
# renames it lake.orig and writes a bash wrapper named lake, which runs dirname and then execs
# lake.orig with LEAN_CC preset. Comparator's sandbox grants execute on the toolchain, on git and
# on what landrun's -ldd finds for the command it is given; for a script that is nothing, so the
# exec of the wrapper is denied on its interpreter ("[landrun:error] permission denied") before
# Lake starts. Rather than widen the sandbox to a shell and coreutils, the rooms resolve `lake`
# to the real binary: a directory holding one symlink, outside every room (nothing confined can
# write to it), which recheck/landrun-shim.sh puts first on the PATH it hands to landrun. It has
# to happen there: `lake env` puts the toolchain's own bin directory back in front of whatever
# PATH this script sets. LEAN_CC is irrelevant here: no room links native code (see confined()
# below for the one variable that does matter, CI), and Comparator's sandbox passes on PATH, HOME
# and LEAN_ABORT_ON_PANIC only.
lake_dir=""
if [ "$(head -c 2 "$RECHECK_TOOLCHAIN_BIN/lake" 2>/dev/null)" = '#!' ]; then
  if [ -x "$RECHECK_TOOLCHAIN_BIN/lake.orig" ]; then
    lake_dir="$out/lake-bin"
    rm -rf "$lake_dir"
    mkdir -p "$lake_dir"
    ln -s "$RECHECK_TOOLCHAIN_BIN/lake.orig" "$lake_dir/lake"
  else
    for c in "${configs[@]}"; do verdict "$c" FAIL 0 "the toolchain's lake ($RECHECK_TOOLCHAIN_BIN/lake) is a script with no lake.orig beside it; Comparator's sandbox cannot run it"; done
    finish
  fi
fi
main_packages="$EX/aeneas/.lake/packages"

# packages_snapshot: one line per fetched package of the source tree: name and checked-out commit.
packages_snapshot() {
  local p
  for p in "$main_packages"/*/; do
    [ -d "$p" ] || continue
    printf '%s %s\n' "$(basename "$p")" "$(git -C "$p" rev-parse HEAD 2>/dev/null || echo NO-GIT)"
  done
}

# populate_room ROOM PATTERN: copy the digested files under PATTERN (a regex over paths) from the
# source tree, regular files only, and require their digests in the room to equal the source's.
populate_room() {
  local room="$1" pattern="$2" list
  list="$(identity_file_list "$EX" | grep -E "$pattern")"
  [ -n "$list" ] || return 1
  ( cd "$EX" && printf '%s\n' "$list" | xargs cp --parents --no-dereference -t "$room" ) || return 1
  if find "$room" -name .lake -print -quit | grep -q .; then return 1; fi
  if [ -n "$(find "$room" ! -type f ! -type d -print -quit)" ]; then return 1; fi
  diff <( cd "$EX" && printf '%s\n' "$list" | xargs sha256sum ) \
       <( cd "$room" && printf '%s\n' "$list" | xargs sha256sum ) > "$room.digest-diff" 2>&1
}

# confined ROOM PKG_DIR -- CMD...: run CMD in PKG_DIR under systemd-run and the outer landrun.
# --best-effort, like Comparator's own landrun call: strict mode demands the newest Landlock ABI
# this landrun knows (V9 for 0.1.17) and refuses to start below it, which no hosted runner kernel
# reaches. What best-effort may silently drop is probed above instead (writes and network).
# Read and execute are granted on the whole tree (--rox /): this layer restricts writes and the
# network, which is all the record claims for it, and an execute allowlist here (it used to be
# /nix/store, the toolchain, the shim and lean4export) holds only where every interpreter lives in
# /nix/store. On any other Linux the toolchain's lake requests the system ELF interpreter and the
# shim's `#!/usr/bin/env` is a system binary, and a nested Landlock domain can only narrow what
# this one grants, so Comparator's own sandbox would inherit the denial. Which files may be
# executed inside a build is Comparator's sandbox's business (its grants, plus the shim's).
#
# CI is the one variable a lakefile of this workspace reads: Aeneas's sets
# `precompileModules := (CI is unset)` on its AeneasMeta library, evaluated when the lakefile is
# elaborated. Lake caches an elaborated configuration under the WORKSPACE's .lake/config, and a
# room's .lake starts empty, so every room elaborates afresh, in its own environment -- from which
# systemd-run, the outer landrun and Comparator's sandbox each drop everything not named. On a
# hosted runner (CI=true) the tree is therefore built without precompilation and the bridge room,
# seeing no CI, configured WITH it: Lake judged AeneasMeta out of date and tried to rebuild it in
# the package directory the room links read-only ("failed to remove output artifacts: permission
# denied ... AeneasMeta/Utils.olean"). A host with no CI never sees this. So CI, when set, is
# handed down all three layers (recheck/landrun-shim.sh does the last one and records it as a
# `--env CI=...` deviation line); when unset it stays unset. A room must configure its linked
# packages exactly as the tree that built them did.
confined() {
  local room="$1" pkg="$2"; shift 3
  local ci_unit=() ci_pass=()
  if [ -n "${CI+x}" ]; then
    ci_unit=(-E "CI=$CI")
    ci_pass=(--env CI)
  fi
  systemd-run --user --wait --pipe --quiet --collect \
    --property=RestrictAddressFamilies=~AF_UNIX \
    -E "PATH=$RECHECK_TOOLCHAIN_BIN:$git_dir:$PATH" \
    -E "HOME=$HOME" \
    -E "COMPARATOR_LEAN4EXPORT=$RECHECK_LEAN4EXPORT" \
    -E "COMPARATOR_LANDRUN=$SHIM" \
    -E "RECHECK_SHIM_LOG=$room/shim.log" \
    -E "RECHECK_EXTRA_RWX=${RECHECK_EXTRA_RWX:-}" \
    -E "RECHECK_LAKE_DIR=$lake_dir" \
    ${ci_unit[@]+"${ci_unit[@]}"} \
    --working-directory "$pkg" \
    -- landrun --best-effort --rox / --rw /dev --rwx "$room" \
         --env PATH --env HOME --env COMPARATOR_LEAN4EXPORT --env COMPARATOR_LANDRUN \
         --env RECHECK_SHIM_LOG --env RECHECK_EXTRA_RWX --env RECHECK_LAKE_DIR \
         ${ci_pass[@]+"${ci_pass[@]}"} \
         -- "$@"
}

run_room() {
  local config="$1"
  local room="$out/rooms/$config" cfg="$out/configs/$config.json" pkg pattern
  local log="$out/$config.log" t0 t1 secs rc last
  case "$config" in
    bridge) pattern='^(lean|aeneas)/'; pkg="$room/aeneas" ;;
    *) pattern='^lean/'; pkg="$room/lean" ;;
  esac
  rm -rf "$room"
  mkdir -p "$room"
  if ! populate_room "$room" "$pattern"; then
    verdict "$config" FAIL 0 "the room's digests differ from the source tree's ($(head -3 "$room.digest-diff" 2>/dev/null | tr '\n' ' '))"
    return
  fi
  RECHECK_EXTRA_RWX=""
  if [ "$config" = bridge ]; then
    if ! bridge_deps_fetched; then
      verdict bridge NOT-RUN 0 "bridge dependencies not fetched (aeneas/.lake/packages)"
      return
    fi
    mkdir -p "$pkg/.lake"
    ln -s "$(realpath "$main_packages")" "$pkg/.lake/packages"
    RECHECK_EXTRA_RWX="$room/lean/.lake"
    # Pre-flight: under exactly Comparator's grants plus the shim's, git must be able to read every
    # linked package's remote. If it cannot, Lake would treat the package as moved and delete it.
    local p name url bad=""
    for p in "$pkg"/.lake/packages/*/; do
      name="$(basename "$p")"
      url="$(cd "$pkg" && confined "$room" "$pkg" -- "$SHIM" --best-effort --ro / --rw /dev -ldd -add-exec \
               --env PATH --env HOME --ro "$pkg" --rwx "$pkg/.lake" --rox "$toolchain_prefix" \
               --rox "$RECHECK_GIT" -- git -C ".lake/packages/$name" remote get-url origin 2>> "$out/bridge.preflight.log")"
      if [ -z "$url" ]; then bad="$bad $name"; echo "pre-flight: no remote read for $name (stderr above)" >> "$out/bridge.preflight.log"; fi
    done
    : > "$room/shim.log"
    if [ -n "$bad" ]; then
      verdict bridge NOT-RUN 0 "pre-flight: git cannot read the remote of$bad inside the sandbox ($(grep -v '^pre-flight:' "$out/bridge.preflight.log" | grep -v '^[[:space:]]*$' | tail -1)); not run, so Lake cannot delete them"
      return
    fi
  fi
  t0="$(date +%s)"
  confined "$room" "$pkg" -- lake env comparator "$cfg" > "$log" 2>&1
  rc=$?
  t1="$(date +%s)"
  secs=$((t1 - t0))
  last="$(grep -v '^[[:space:]]*$' "$log" | tail -1)"

  [ -n "$lake_dir" ] && printf '%s PATH: lake is <toolchain>/bin/lake.orig (the toolchain'"'"'s lake is a shell wrapper around it)\n' "$config" >> "$DEVIATIONS"
  if [ -s "$room/shim.log" ]; then
    grep '^extra ' "$room/shim.log" | sed -e 's/^extra //' -e "s|$room|<room>|g" \
      -e "s|$toolchain_prefix|<toolchain>|g" |
      awk '{ for (i = 1; i < NF; i += 2) print $i, $(i + 1) }' |
      LC_ALL=C sort -u | sed "s|^|$config |" >> "$DEVIATIONS"
  fi

  case "$config" in
    core|bridge)
      if [ "$rc" -eq 0 ] && [ "$last" = "Your solution is okay!" ] &&
         grep -qx 'Lean default kernel accepts the solution' "$log"; then
        verdict "$config" OK "$secs" "Your solution is okay!"
      else
        verdict "$config" FAIL "$secs" "exit $rc; last line: ${last:-<none>}"
      fi
      ;;
    flagged-*)
      local expect="$out/configs/$config.expect" h matched=false
      while IFS= read -r h; do
        [ -z "$h" ] && continue
        [ "$last" = "uncaught exception: Illegal axiom detected: '$h'" ] && matched=true
      done < "$expect"
      if [ "$rc" -ne 0 ] && $matched; then
        verdict "$config" EXPECTED-REJECTION "$secs" "${last#uncaught exception: }"
      else
        verdict "$config" FAIL "$secs" "exit $rc; expected Illegal axiom detected for $(tr '\n' ' ' < "$expect"); last line: ${last:-<none>}"
      fi
      ;;
  esac
}

before="$(packages_snapshot)"
for c in "${configs[@]}"; do
  run_room "$c"
done
after="$(packages_snapshot)"
if [ "$before" != "$after" ]; then
  echo "recheck-comparator.sh: the source tree's aeneas/.lake/packages CHANGED during the run" >&2
  diff <(printf '%s\n' "$before") <(printf '%s\n' "$after") >&2
  verdict packages FAIL 0 "aeneas/.lake/packages changed during the run"
fi
LC_ALL=C sort -u -o "$DEVIATIONS" "$DEVIATIONS"
finish
