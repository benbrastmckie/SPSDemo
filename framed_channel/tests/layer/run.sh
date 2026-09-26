#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# tests/layer/run.sh -- fixture tests for check.sh's layer import rules.
#
# The gate's layer stage is the only thing standing between the definitions layer and a proof
# module, and between the generic composition and a queue model. Its rules are extended regexes
# over paths, so a layout change can quietly move a file OUT of a rule's path regex: the rule then
# forbids nothing and the stage still prints [ok]. These cases pin both halves of each rule -- the
# import that must be rejected, and the import that must not be -- at the paths the layout rule
# fixes.
#
# No copy of the rules lives here. The runner extracts check.sh's own `# >>> layer-rules` block
# (its regex arrays, the derived queue-model list, and the `layer_violations` matcher the stage
# itself calls) and applies it to fixture module paths and import lists, so a rule that drifts in
# check.sh drifts here too. The queue-model list is derived from the real lean/FramedChannel/Model
# tree, so `<queue-model>` below is a real unit name, not a typed one.
#
# Usage: bash tests/layer/run.sh [-h | --help]      (from any directory)
# Requires: bash >= 4.4, coreutils. No Lean toolchain, no network, no build.
# Exit: 0 every case behaves as recorded, 1 otherwise, 2 usage error.

set -u

case "${1:-}" in
  "") ;;
  -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
  *) echo "run.sh: unknown argument '$1' (try --help)" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EX="$(cd "$HERE/../.." && pwd)"

block="$(sed -n '/^# >>> layer-rules/,/^# <<< layer-rules/p' "$EX/check.sh")"
if [ -z "$block" ]; then
  echo "[FAIL] check.sh has no '# >>> layer-rules' ... '# <<< layer-rules' block to extract"
  echo "       (the markers are load-bearing: this self-test reads the gate's real rules through them)"
  exit 1
fi
# shellcheck disable=SC2034  # EX is read by the extracted block
eval "$block"

# shellcheck disable=SC2154  # queue_model_units is assigned by the extracted block
if [ "${#queue_model_units[@]}" -eq 0 ]; then
  echo "[FAIL] the extracted block derived no queue model from lean/FramedChannel/Model"
  exit 1
fi
QM="${queue_model_units[0]}"
echo "note: derived queue models: ${queue_model_units[*]} (cases below use '$QM')"

# name|module path relative to EX|space-separated imports|expect ("reject" or "allow")
CASES=(
  "a composition theorem module may not import a queue model|lean/FramedChannel/Composition/Widget/Theorems.lean|FramedChannel.Model.${QM}.Theorems|reject"
  "a composition definitions module may not import a queue model|lean/FramedChannel/Composition/Widget/Defs.lean|FramedChannel.Model.${QM}.Defs|reject"
  "a composition theorem module may import a specification|lean/FramedChannel/Composition/Widget/Theorems.lean|FramedChannel.Spec.Queue|allow"
  "Instances.lean is deliberately outside the composition rule|lean/FramedChannel/Composition/Widget/Instances.lean|FramedChannel.Model.${QM}.Theorems|allow"
  "a core definitions module may not import a proof module|lean/FramedChannel/Model/Widget/Defs.lean|FramedChannel.Model.${QM}.Theorems|reject"
  "a core definitions module may import a specification and a sibling Defs|lean/FramedChannel/Model/Widget/Defs.lean|FramedChannel.Spec.Queue FramedChannel.Model.${QM}.Defs|allow"
  "a bridge definitions module may not import a proof module|aeneas/FramedChannelAeneas/Bridge/Widget/Defs.lean|FramedChannelAeneas.Bridge.Queue.Transport|reject"
  "a bridge definitions module may import extraction and a sibling Defs|aeneas/FramedChannelAeneas/Bridge/Widget/Defs.lean|FramedChannelAeneas.Extracted.Funs FramedChannelAeneas.Bridge.Queue.Defs|allow"
  "a definitions module named FooDefs is no longer a definitions module|lean/FramedChannel/Model/WidgetDefs.lean|FramedChannel.Model.${QM}.Theorems|allow"
  "a Challenge module may not import a proof module|aeneas/FramedChannelAeneasChallenge/Widget.lean|FramedChannelAeneas.Bridge.Widget.Refinement|reject"
  "a Challenge module may import definitions, extraction and Aeneas|aeneas/FramedChannelAeneasChallenge/Widget.lean|FramedChannelAeneas.Bridge.Widget.Defs FramedChannelAeneas.Extracted.Funs Aeneas|allow"
  "a model may not import a composition|lean/FramedChannel/Model/Widget/Theorems.lean|FramedChannel.Composition.Channel.Theorems|reject"
  "the core package may not import Aeneas|lean/FramedChannel/Model/Widget/Theorems.lean|Aeneas.Std|reject"
  "nothing imports an Evidence module|aeneas/FramedChannelAeneas/Bridge/Widget/Refinement.lean|FramedChannel.Evidence.Countermodels|reject"
)

failures=0
for entry in "${CASES[@]}"; do
  IFS='|' read -r name rel imports expect <<< "$entry"
  # shellcheck disable=SC2086  # the import list is intentionally word-split, as in the stage
  out="$(layer_violations "$rel" $imports)"
  if [ -n "$out" ]; then got=reject; else got=allow; fi
  if [ "$got" = "$expect" ]; then
    echo "[ok] $name ($got)"
  else
    echo "[FAIL] $name: the rules $got this import, expected $expect"
    [ -n "$out" ] && sed 's/^/    /' <<< "$out"
    failures=$((failures + 1))
  fi
done

# No layer rule may TYPE a component name. This is checked against the block's SOURCE, not its
# expanded values: `${QUEUE_MODELS_RE}` legitimately expands to the derived unit names, and the
# library prefixes `FramedChannel`/`FramedChannelAeneas` are package names, not components. Both
# are masked out first; anything left is a typed component name, the defect this rule set no
# longer carries. Comment lines are dropped -- prose may say "channel" in passing; a rule may not.
component_names='RingBuffer|ListQueue|VecQueue|Varint|Zigzag|Crc8|Stuff|Channel|QueueDefs|QueueInstance'
masked="$(printf '%s\n' "$block" \
  | grep -v '^[[:space:]]*#' \
  | sed -e 's/\${QUEUE_MODELS_RE}/DERIVED/g' \
        -e 's/FramedChannelAeneasChallenge/LIBAENEASCHALLENGE/g' \
        -e 's/FramedChannelChallenge/LIBCHALLENGE/g' \
        -e 's/FramedChannelAeneas/LIBAENEAS/g' \
        -e 's/FramedChannel/LIB/g')"
if hits="$(printf '%s\n' "$masked" | grep -nE "$component_names")"; then
  echo "[FAIL] a layer rule types a component name (it must derive it or not need it):"
  sed 's/^/    /' <<< "$hits"
  failures=$((failures + 1))
else
  echo "[ok] no layer rule types a component name (the queue-model list is derived, not typed)"
fi

if [ $failures -ne 0 ]; then
  echo "tests/layer/run.sh: $failures case(s) did not behave as recorded"
  exit 1
fi
echo "tests/layer/run.sh: ${#CASES[@]} case(s) and the no-component-name check behaved as recorded"
