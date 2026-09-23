#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/landrun-shim/run.sh -- fixture tests for recheck/landrun-shim.sh's environment hand-down.
#
# A Comparator room elaborates every lakefile afresh, in the environment Comparator's sandbox
# leaves it, and Aeneas's lakefile precompiles its AeneasMeta library only where CI is unset. A
# room that does not see the CI the tree was built under configures the read-only linked Aeneas
# package differently and Lake tries to rebuild it in place: that is how the bridge room failed on
# every hosted runner while passing on every development host. These cases run the shim against a
# stub `landrun` that prints its arguments and hold in place that CI is handed down exactly when
# it is set, that Comparator's own arguments follow unchanged and in order, and that
# scripts/recheck-comparator.sh names CI at both outer layers (systemd-run and the outer landrun).
#
# Usage: bash tests/landrun-shim/run.sh [-h | --help]      (from any directory)
# Requires: bash, git, ldd, grep, mktemp. Linux only (the shim is); elsewhere it reports a skip.
# Exit: 0 every case behaves as recorded (or skipped off Linux), 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"
SHIM="$EX/recheck/landrun-shim.sh"
DRIVER="$EX/scripts/recheck-comparator.sh"

if [ "$(uname -s)" != Linux ]; then
  echo "[skip] landrun-shim: the shim is Linux-only ($(uname -s) here)"
  exit 0
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/bin" "$work/room"
cat > "$work/bin/landrun" <<'STUB'
#!/usr/bin/env bash
printf '%s\n' "$@"
STUB
chmod +x "$work/bin/landrun"

failures=0
ok() { echo "[ok] $1"; }
bad() { echo "[FAIL] $1"; failures=$((failures + 1)); }

# run_shim OUTFILE [ENV_ASSIGNMENT...] -- runs the shim from inside the room with the stub first
# on PATH and Comparator-shaped arguments; CI is removed from the environment unless assigned.
run_shim() {
  local outfile="$1"; shift
  ( cd "$work/room" && env -u CI -u RECHECK_LAKE_DIR -u RECHECK_EXTRA_RWX -u RECHECK_SHIM_LOG \
      "$@" PATH="$work/bin:$PATH" bash "$SHIM" --best-effort --ro / -- lake build Target ) > "$outfile" 2>&1
}

# has_pair FILE FLAG VALUE -- FLAG on one line immediately followed by VALUE on the next.
has_pair() { grep -x -A1 -- "$2" "$1" | grep -qx -- "$3"; }

run_shim "$work/unset.out"
if grep -q '^CI=' "$work/unset.out"; then bad "CI unset: the shim must not invent a CI for the room"
else ok "CI unset: no --env CI handed to landrun"; fi

run_shim "$work/true.out" CI=true
if has_pair "$work/true.out" --env CI=true; then ok "CI=true: handed down as --env CI=true"
else bad "CI=true: --env CI=true missing from landrun's arguments"; fi

run_shim "$work/empty.out" CI=
if has_pair "$work/empty.out" --env CI=; then ok "CI set but empty: still handed down (a lakefile tests whether it is set)"
else bad "CI set but empty: --env CI= missing from landrun's arguments"; fi

want="$(printf '%s\n' --best-effort --ro / -- lake build Target)"
for f in unset true empty; do
  if [ "$(tail -n 7 "$work/$f.out")" = "$want" ]; then ok "$f: Comparator's own arguments follow unchanged and in order"
  else bad "$f: Comparator's own arguments were altered or reordered"; fi
done

# shellcheck disable=SC2016
if grep -q -- '-E "CI=\$CI"' "$DRIVER" && grep -q -- '--env CI' "$DRIVER"; then
  ok "recheck-comparator.sh hands CI through systemd-run and the outer landrun"
else
  bad "recheck-comparator.sh no longer hands CI through systemd-run (-E \"CI=\$CI\") and the outer landrun (--env CI)"
fi

if [ "$failures" -eq 0 ]; then echo "landrun-shim: PASS"; exit 0; fi
echo "landrun-shim: $failures failure(s)"; exit 1
