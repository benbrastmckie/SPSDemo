#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# refresh-candidates.sh -- regenerate certificate/candidates.txt, the Select candidate set.
#
# From the pinned charon LLBC of the whole crate: one row per local item, `in-subset` or
# `excluded` with every failed criterion named. The criteria, their scope and the human decision
# over this file (certificate/approvals.yaml, via approve.sh): certificate/README.md. Byte-stable.
#
# Columns (tab-separated, rows sorted with LC_ALL=C, after a `#` header):
#   1 extracted Lean name (`framed_channel.<...>`, or `-` when not extracted)
#   2 Rust path (inherent impl blocks render as `{impl}`, trait impls as `{impl <Trait>}`)
#   3 source span `file:line:col-line:col`
#   4 `pub` / `priv`
#   5 kind: `fn` / `trait-impl` / `const`
#   6 `derived:<Trait>` or `-`
#   7 verdict: `in-subset` / `excluded`
#   8 reason (`-` when in-subset; `; `-separated when several criteria fail)
#
# Usage: bash scripts/refresh-candidates.sh [--check] [--llbc FILE] [-h | --help] (from framed_channel/)
#   --check       regenerate into a temporary file and diff; write nothing
#   --llbc FILE   classify this LLBC instead of running charon (check.sh reuses its extraction's)
#
# Requires: bash >= 4.4, jq, and without --llbc charon at the revision pinned in ../flake.lock
# (nix develop .#extraction, or bash full-gate.sh). The LLBC schema read is that charon's; a
# missing field fails the run.
# Exit: 0 written or current, 1 stale under --check or classification failed, 2 usage error or
# missing prerequisite.

set -u

EX="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CANDIDATES="$EX/certificate/candidates.txt"
FUNS="$EX/aeneas/FramedChannelAeneas/Extracted/Funs.lean"
LIB_RS="$EX/rust/src/lib.rs"

# Concurrency, IO and interior-mutability paths, matched against every translated declaration
# (local or library). Charon translates exactly what the crate reaches, so an empty match is a
# sound crate-wide check; it is not attributed per item (see the note at the per-item jq program).
DENY_RE='^(std::(thread|sync|io|fs|net|process|env|time)|core::(cell|sync)|alloc::(rc|sync))(::|$)'

check_only=false
llbc=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --check) check_only=true; shift ;;
    --llbc)
      [ "$#" -ge 2 ] || { echo "refresh-candidates.sh: --llbc needs a file" >&2; exit 2; }
      llbc="$2"; shift 2 ;;
    -h|--help) awk 'NR > 2 && !/^#/ { exit } NR > 2 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "refresh-candidates.sh: unknown argument '$1' (expected --check, --llbc FILE)" >&2
       exit 2 ;;
  esac
done

command -v jq > /dev/null 2>&1 || { echo "refresh-candidates.sh: jq is not on PATH" >&2; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

if [ -z "$llbc" ]; then
  if ! command -v charon > /dev/null 2>&1; then
    echo "refresh-candidates.sh: charon is not on PATH." >&2
    echo "  From the repository root: nix develop .#extraction --command bash framed_channel/scripts/refresh-candidates.sh (or bash full-gate.sh)" >&2
    exit 2
  fi
  # A private target directory, so the LLBC never depends on incremental state in rust/target.
  if ! ( cd "$EX/rust" && CARGO_TARGET_DIR="$work/target" \
         charon cargo --preset=aeneas --dest-file "$work/framed_channel.llbc" ) \
         > "$work/charon.log" 2>&1; then
    echo "refresh-candidates.sh: charon failed" >&2
    cat "$work/charon.log" >&2
    exit 1
  fi
  llbc="$work/framed_channel.llbc"
fi
[ -f "$llbc" ] || { echo "refresh-candidates.sh: no LLBC at $llbc" >&2; exit 1; }
[ -f "$FUNS" ] || { echo "refresh-candidates.sh: $FUNS is missing" >&2; exit 1; }

# Fail loudly on a schema this script was not written for.
if ! jq -e '
    (.charon_version | type == "string")
    and (.has_errors == false)
    and (.translated.fun_decls | type == "array")
    and (.translated.trait_impls | type == "array")
    and (.translated.trait_decls | type == "array")
    and (.translated.files | type == "array")
    and ([.translated.fun_decls[] | select(. != null) | select(.item_meta.is_local)] | length > 0)
    and ([.translated.fun_decls[] | select(. != null) | select(.item_meta.is_local)
          | (.item_meta.span.Untagged.data.beg.line | type == "number")
            and (.signature.is_unsafe | type == "boolean")
            and (.item_meta.attr_info.public | type == "boolean")
            and (.item_meta.source_text | type == "string" or type == "null")] | all)
  ' "$llbc" > /dev/null; then
  echo "refresh-candidates.sh: $llbc is not an error-free LLBC of the schema this script reads" >&2
  echo "  (missing field, has_errors, or no local items); refusing to classify it" >&2
  exit 1
fi

charon_version="$(jq -r '.charon_version' "$llbc")"

if grep -qE '^#!\[forbid\(unsafe_code\)\]' "$LIB_RS"; then
  crate_forbids=true
else
  crate_forbids=false
fi

# Every translated declaration path matching the denylist (local or library).
jq -r --arg re "$DENY_RE" '
  def pname: map(if .Ident then .Ident[0] elif .Impl then "{impl}" else "?" end) | join("::");
  [.translated.fun_decls[], .translated.type_decls[], .translated.trait_decls[],
   .translated.global_decls[] | select(. != null) | .item_meta.name | pname]
  | map(select(test($re))) | unique | .[]
' "$llbc" > "$work/denied"

# The Funs.lean function docstrings: `<file>:<span>\t<Lean name>`. A docstring opens with
# `/-- [framed_channel::...]`; loop and loop-body docstrings (`]: loop ...`) and trait-record
# docstrings (`/-- Trait implementation:`) are not items. The span key is the docstring's
# `Source: 'src/x.rs', lines a:b-c:d`; the name is that of the next `def`.
awk '
  /^\/-- \[framed_channel::/ { doc = ($0 ~ /\]: loop/) ? "" : "item"; span = ""; next }
  /^\/-- / { doc = ""; next }
  doc == "item" && /Source: '\''/ {
    s = $0
    sub(/.*Source: '\''/, "", s)
    file = s; sub(/'\''.*/, "", file)
    sub(/.*lines /, "", s); sub(/[^0-9:-].*$/, "", s)
    span = file ":" s
    next
  }
  doc == "item" && span != "" && /(^|[] ])def / {
    n = $0; sub(/.*def /, "", n); sub(/[ :].*$/, "", n)
    print span "\tframed_channel." n
    doc = ""; span = ""
  }
' "$FUNS" | LC_ALL=C sort > "$work/extracted"

if [ -n "$(cut -f1 "$work/extracted" | uniq -d)" ]; then
  echo "refresh-candidates.sh: two Funs.lean items share a source span; the join is ambiguous:" >&2
  cut -f1 "$work/extracted" | uniq -d >&2
  exit 1
fi

# One JSON record per local function declaration. Note on attribution: the LLBC hash-conses
# repeated sub-terms (`{"Value": [id, term]}` defines, `{"Deduplicated": id}` refers) in several
# independent id spaces, so a per-item walk of callees or types cannot be resolved soundly from
# the JSON alone. The per-item checks therefore read only unshared fields (unsafety, visibility,
# the source text, the span, the trait-impl attributes), and the callee denylist is the crate-wide
# check above.
jq -c '
  def pname: map(if .Ident then .Ident[0] elif .Impl then "{impl}" else "?" end) | join("::");
  .translated as $t
  | ($t.files | map(select(. != null)) | map({key: (.id | tostring), value: (.name.Local // .name.Virtual // "?")}) | from_entries) as $files
  | $t.fun_decls[] | select(. != null) | select(.item_meta.is_local)
  | .item_meta.span.Untagged.data as $sp
  | (if (.src | type) == "object" and (.src | has("TraitImpl")) then
       $t.trait_impls[.src.TraitImpl.impl_ref.id]
     else null end) as $impl
  | (if $impl == null then null else ($t.trait_decls[$impl.impl_trait.id].item_meta.name | pname) end) as $trait
  | {
      path: (.item_meta.name
             | map(if .Ident then .Ident[0]
                   elif .Impl then (if $trait == null then "{impl}" else "{impl \($trait)}" end)
                   else "?" end)
             | join("::")),
      span: "\($files[$sp.file_id | tostring]):\($sp.beg.line):\($sp.beg.col)-\($sp.end.line):\($sp.end.col)",
      public: .item_meta.attr_info.public,
      unsafe: .signature.is_unsafe,
      kind: (if (.src | type) == "string" then "fn"
             elif (.src | has("TraitImpl")) then "trait-impl"
             elif (.src | has("GlobalInitializer")) then "const"
             else "other" end),
      derived: (if $impl == null then null
                elif ([$impl.item_meta.attr_info.attributes[] | tojson | test("AutomaticallyDerived")] | any)
                then ($trait | split("::") | last) else null end),
      source: (.item_meta.source_text // "")
    }
' "$llbc" > "$work/items.jsonl"

denied_count="$(grep -c . "$work/denied")"

while IFS= read -r rec; do
  path="$(jq -r .path <<< "$rec")"
  span="$(jq -r .span <<< "$rec")"
  public="$(jq -r .public <<< "$rec")"
  unsafe="$(jq -r .unsafe <<< "$rec")"
  kind="$(jq -r .kind <<< "$rec")"
  derived="$(jq -r '.derived // "-"' <<< "$rec")"
  # Line comments stripped, so prose may name the forbidden forms.
  source="$(jq -r .source <<< "$rec" | sed 's|//.*$||')"

  reasons=()
  $crate_forbids || reasons+=("crate lacks #![forbid(unsafe_code)]")
  [ "$denied_count" -eq 0 ] || reasons+=("crate reaches denylisted path(s): $(tr '\n' ' ' < "$work/denied" | sed 's/ $//')")
  [ "$unsafe" = false ] || reasons+=("unsafe fn")
  if grep -qE '\*[[:space:]]*(const|mut)[[:space:]]' <<< "$source"; then
    reasons+=("raw pointer type in source")
  fi
  if grep -qE '\bstatic[[:space:]]+mut\b' <<< "$source"; then
    reasons+=("static mut in source")
  fi
  [ "$kind" = other ] && reasons+=("unrecognised item kind")
  lean="$(awk -F'\t' -v k="$span" '$1 == k { print $2 }' "$work/extracted")"
  if [ -z "$lean" ]; then
    lean="-"
    reasons+=("not extracted")
  fi
  [ "$public" = true ] && vis=pub || vis=priv
  [ "$derived" = "-" ] || derived="derived:$derived"

  if [ ${#reasons[@]} -eq 0 ]; then
    verdict=in-subset; reason="-"
  else
    verdict=excluded
    reason="$(printf '%s; ' "${reasons[@]}" | sed 's/; $//')"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$lean" "$path" "$span" "$vis" "$kind" "$derived" "$verdict" "$reason"
done < "$work/items.jsonl" | LC_ALL=C sort > "$work/rows"

rows="$(grep -c . "$work/rows")"
in_subset="$(awk -F'\t' '$7 == "in-subset"' "$work/rows" | grep -c .)"
derived_rows="$(awk -F'\t' '$6 != "-"' "$work/rows" | grep -c .)"

{
  echo "# framed_channel Select candidates (generated by refresh-candidates.sh; do not edit)"
  echo "# charon: $charon_version (whole-crate charon cargo --preset=aeneas over rust/)"
  echo "# extraction joined: aeneas/FramedChannelAeneas/Extracted/Funs.lean (by source span)"
  echo "# crate forbids unsafe_code (rust/src/lib.rs): $($crate_forbids && echo yes || echo NO)"
  echo "# translated declarations matching the concurrency/IO/interior-mutability denylist: $denied_count"
  echo "# items: $rows local; $in_subset in-subset; $((rows - in_subset)) excluded; $derived_rows derived impls"
  echo "# scope: syntactic checks over the crate's own LLBC items; std internals are not audited (G3)"
  echo "# columns: lean_name	rust_path	span	visibility	kind	derived	verdict	reason"
  cat "$work/rows"
} > "$work/candidates.txt"

if $check_only; then
  if [ ! -f "$CANDIDATES" ]; then
    echo "refresh-candidates.sh: certificate/candidates.txt is missing; run 'bash scripts/refresh-candidates.sh'" >&2
    exit 1
  fi
  if ! diff -u "$CANDIDATES" "$work/candidates.txt" > "$work/diff"; then
    sed -n '1,60p' "$work/diff"
    echo "refresh-candidates.sh: certificate/candidates.txt is stale; re-read the diff, then run 'bash scripts/refresh-candidates.sh'" >&2
    exit 1
  fi
  echo "refresh-candidates.sh: certificate/candidates.txt is current ($rows items, $in_subset in-subset)"
  exit 0
fi

mkdir -p "$(dirname "$CANDIDATES")"
if cmp -s "$work/candidates.txt" "$CANDIDATES"; then
  echo "refresh-candidates.sh: certificate/candidates.txt already current ($rows items, $in_subset in-subset)"
else
  cp "$work/candidates.txt" "$CANDIDATES"
  echo "refresh-candidates.sh: wrote certificate/candidates.txt ($rows items, $in_subset in-subset; re-read the diff before committing)"
fi
