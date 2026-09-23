# shellcheck shell=bash
# SPDX-License-Identifier: Apache-2.0
# approval-digests.sh -- what an approval record is bound to, shared by approve.sh and
# check-approvals.sh so the writer and the checker cannot disagree. SOURCED.
#
#   source_sha256 [EX]       sha256 over the sorted `sha256sum` lines of rust/src/*.rs,
#                            rust/Cargo.toml and rust/Cargo.lock (tests and rustfmt.toml are not
#                            the Rust being selected); any edit, a comment included, changes it --
#                            EXCEPT the root package's own `version` field in Cargo.toml and in
#                            Cargo.lock's own `[[package]]` block, which is excluded from the
#                            digest by cargo_version_normalized_sha256 below (it affects no
#                            compiled behavior and no proof, so it is metadata, not content;
#                            dependency versions, the lockfile format version, `edition` and every
#                            other field remain fully hashed)
#   cargo_root_package_name TOML
#                            the `name` value from TOML's `[package]` table; nothing and exit 1
#                            when there is no `[package]` table or no `name` in it
#   cargo_version_normalized_sha256 FILE [ROOT_NAME]
#                            one line in exact `sha256sum` format (`<64 hex><space><space><FILE as
#                            given>`) over a version-normalized view of FILE, dispatched on FILE's
#                            basename:
#                              Cargo.toml: every `version = ...` line inside the `[package]` table
#                                is dropped; every other table (including `[dependencies]`) is
#                                hashed verbatim.
#                              Cargo.lock: the lockfile's own root `[[package]]` block (the one
#                                whose `name` equals ROOT_NAME) has its `version = ...` line
#                                dropped; every other `[[package]]` block (a dependency) and the
#                                leading format preamble (`version = 4`) are hashed verbatim.
#                              Any other basename is a caller error (exit 2). A Cargo.lock call
#                                with an empty or unresolvable ROOT_NAME prints nothing and exits 1
#                                -- it never falls back to stripping nothing or everything.
#                            Runs under `LC_ALL=C` with POSIX awk only, so the digest is
#                            byte-identical across the Linux and macOS runners that compare it.
#   candidates_sha256 [EX]   sha256 of certificate/candidates.txt
#   approver_valid STRING    true for "Name <email>"
#   approval_commit DIGEST [EX]
#                            the oldest commit that recorded DIGEST in certificate/approvals.yaml
#   approvals_normalize FILE the records of an approvals file (see below)
#   insubset_candidates FILE [--with-derived]
#                            every in-subset candidate name (column 1) of a
#                            certificate/candidates.txt-shaped tab FILE, sorted unique;
#                            --with-derived instead prints "<name><TAB><column 6>" per row,
#                            sorted but not deduplicated (a caller needing the derived-from
#                            marker alongside the name, e.g. approve.sh's review, wants every
#                            row, not one per name)
#   imported_defs REL [EX]   the files of this example that Challenge module REL imports
#                            (depends on lean_imports, scripts/lib/packages.sh)
#
# EX defaults to two directories up from this file (framed_channel/); hashed paths are relative
# to it, so a digest does not depend on where the repository is checked out. A digest function
# prints nothing and fails when an input is missing. Requires: coreutils (sha256sum), find, awk;
# git for approval_commit.

approval_digests_ex() {
  if [ -n "${1:-}" ]; then
    echo "$1"
  else
    (cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
  fi
}

# cargo_root_package_name TOML -- print the `name` value of TOML's `[package]` table. Prints
# nothing and returns 1 when there is no `[package]` table or no `name` key in it (e.g. a
# workspace-shaped Cargo.toml). POSIX awk only; buffers no state past the current table name, so
# key order within the table does not matter.
cargo_root_package_name() {
  local toml="$1"
  LC_ALL=C awk '
    {
      trimmed = $0
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", trimmed)
      if (trimmed ~ /^\[\[[^]]*\]\]$/ || trimmed ~ /^\[[^]]*\]$/) { table = trimmed; next }
      if (table == "[package]" && $0 ~ /^[[:space:]]*name[[:space:]]*=/) {
        v = $0
        sub(/^[[:space:]]*name[[:space:]]*=[[:space:]]*/, "", v)
        sub(/[[:space:]]*(#.*)?$/, "", v)
        gsub(/"/, "", v)
        print v
        found = 1
        exit
      }
    }
    END { if (!found) exit 1 }
  ' "$toml"
}

# cargo_version_normalized_sha256 FILE [ROOT_NAME] -- one line in exact `sha256sum` format
# (`<64 hex><space><space><FILE as given>`) over a version-normalized view of FILE. Only the root
# package's own `version` field is excluded; every dependency version, the lockfile format
# version, and every other field (edition, rust-version, license, features, targets, ...) is
# hashed verbatim. Dispatches on FILE's basename:
#   Cargo.toml   drops every `version = ...` line while the current TOML table is exactly
#                `[package]`; every other table (including `[dependencies]`) is untouched.
#   Cargo.lock   buffers each `[[package]]` block whole (so key order inside the block does not
#                matter) and drops only the `version = ...` line of the block whose own `name`
#                equals ROOT_NAME; every other block (a dependency) and the leading format
#                preamble (`version = 4`) are hashed verbatim. Requires a non-empty ROOT_NAME:
#                with an empty or unresolvable one, prints nothing and returns 1 rather than
#                falling back to stripping nothing or everything.
#   (other)      a caller error -- this transform applies to exactly these two paths -- returns 2.
# Runs under LC_ALL=C with POSIX-only awk constructs, so the digest is byte-identical whether
# computed on Linux or macOS.
cargo_version_normalized_sha256() {
  local file="$1" root_name="${2:-}" base hex
  base="$(basename -- "$file")"
  case "$base" in
    Cargo.toml)
      hex="$(LC_ALL=C awk '
        {
          trimmed = $0
          gsub(/^[[:space:]]+|[[:space:]]+$/, "", trimmed)
          if (trimmed ~ /^\[\[[^]]*\]\]$/ || trimmed ~ /^\[[^]]*\]$/) { table = trimmed; print; next }
          if (table == "[package]" && $0 ~ /^[[:space:]]*version[[:space:]]*=/) next
          print
        }
      ' "$file" | LC_ALL=C sha256sum | cut -d' ' -f1)" || return 1
      ;;
    Cargo.lock)
      [ -n "$root_name" ] || return 1
      LC_ALL=C awk -v root="$root_name" '
        /^\[\[package\]\]$/ { inpkg = 1; next }
        inpkg && /^[[:space:]]*name[[:space:]]*=/ {
          v = $0
          sub(/^[[:space:]]*name[[:space:]]*=[[:space:]]*/, "", v)
          sub(/[[:space:]]*(#.*)?$/, "", v)
          gsub(/"/, "", v)
          if (v == root) { found = 1; exit }
          inpkg = 0
        }
        END { exit !found }
      ' "$file" || return 1
      hex="$(LC_ALL=C awk -v root="$root_name" '
        function flush(   i) {
          if (nbuf > 0) {
            for (i = 1; i <= nbuf; i++) {
              if (blockname == root && buf[i] ~ /^[[:space:]]*version[[:space:]]*=/) continue
              print buf[i]
            }
          }
          nbuf = 0
          blockname = ""
          delete buf
        }
        /^\[\[package\]\]$/ {
          flush()
          nbuf++
          buf[nbuf] = $0
          next
        }
        nbuf > 0 {
          nbuf++
          buf[nbuf] = $0
          if ($0 ~ /^[[:space:]]*name[[:space:]]*=/) {
            v = $0
            sub(/^[[:space:]]*name[[:space:]]*=[[:space:]]*/, "", v)
            sub(/[[:space:]]*(#.*)?$/, "", v)
            gsub(/"/, "", v)
            blockname = v
          }
          next
        }
        { print }
        END { flush() }
      ' "$file" | LC_ALL=C sha256sum | cut -d' ' -f1)" || return 1
      ;;
    *)
      return 2
      ;;
  esac
  [ -n "$hex" ] || return 1
  printf '%s  %s\n' "$hex" "$file"
}

source_sha256() {
  local ex
  ex="$(approval_digests_ex "${1:-}")"
  [ -d "$ex/rust/src" ] && [ -f "$ex/rust/Cargo.toml" ] && [ -f "$ex/rust/Cargo.lock" ] || return 1
  (
    cd "$ex" || exit 1
    set -o pipefail
    root="$(cargo_root_package_name rust/Cargo.toml)" || root=""
    {
      find rust/src -maxdepth 1 -type f -name '*.rs'
      printf '%s\n' rust/Cargo.toml rust/Cargo.lock
    } | LC_ALL=C sort | (
      set -o pipefail
      while IFS= read -r f; do
        case "$f" in
          rust/Cargo.toml) cargo_version_normalized_sha256 "$f" || exit 1 ;;
          rust/Cargo.lock) cargo_version_normalized_sha256 "$f" "$root" || exit 1 ;;
          *) sha256sum "$f" || exit 1 ;;
        esac
      done
    ) | sha256sum | cut -d' ' -f1
  )
}

candidates_sha256() {
  local ex
  ex="$(approval_digests_ex "${1:-}")"
  [ -f "$ex/certificate/candidates.txt" ] || return 1
  sha256sum "$ex/certificate/candidates.txt" | cut -d' ' -f1
}

approver_valid() {
  [[ "$1" =~ ^[^[:space:]\<\>][^\<\>]*[^[:space:]\<\>][[:space:]]+\<[^[:space:]\<\>@]+@[^[:space:]\<\>@]+\>$ ]]
}

# approver_matches_by APPROVER BY: an agent approver is named "... (agent) <email>", a person is not.
approver_matches_by() {
  case "$2" in
    agent) [[ "$1" == *"(agent) <"* ]] ;;
    person) [[ "$1" != *"(agent)"* ]] ;;
    *) return 1 ;;
  esac
}

approval_commit() {
  local ex
  ex="$(approval_digests_ex "${2:-}")"
  git -C "$ex" log --format=%h -S"$1" -- certificate/approvals.yaml 2>/dev/null | tail -1
}

# approvals_normalize FILE: read certificate/approvals.yaml (the fixed, hand-written shape below)
# and print one tab-separated record per fact, or print `parse-error<TAB><line>: <why>` lines and
# return 1. Only this shape is accepted; any other key, indentation or list form is a parse error,
# so the file cannot carry something the gate silently ignores.
#
#   selection:
#     candidates_sha256: <hex>
#     source_sha256: <hex>
#     selected:
#       - <extracted Lean name>
#     declined:
#       - name: <extracted Lean name>
#         reason: "<why>"
#     approver: "Name <email>"
#     by: person | agent
#     date: YYYY-MM-DD
#   specification:
#     - challenge: <Challenge module>
#       spec_digest: <nat>
#       approver: "Name <email>"
#       by: person | agent
#       date: YYYY-MM-DD
#
# Output records:
#   sel<TAB>candidates_sha256|source_sha256|approver|by|date<TAB><value>
#   sel<TAB>selected<TAB><name>
#   sel<TAB>declined<TAB><name><TAB><reason>
#   spec<TAB><index><TAB>challenge|spec_digest|approver|by|date<TAB><value>
# Comments (`#` at the start of a line, after optional spaces) and blank lines are ignored. Values
# may be double-quoted; the quotes are removed.
approvals_normalize() {
  awk '
    function unq(v) {
      sub(/^[ \t]+/, "", v); sub(/[ \t]+$/, "", v)
      if (v ~ /^".*"$/) { v = substr(v, 2, length(v) - 2) }
      return v
    }
    function err(why) { printf "parse-error\t%d: %s\n", NR, why; bad = 1 }
    /^[ \t]*#/ || /^[ \t]*$/ { next }
    /^selection:[ \t]*$/ { top = "sel"; sub1 = ""; nsel++; next }
    /^specification:[ \t]*$/ { top = "spec"; nspec++; next }
    /^[^ ]/ { err("unknown top-level key: " $0); top = ""; next }
    top == "sel" && /^  (candidates_sha256|source_sha256|approver|by|date):/ {
      k = $1; sub(/:$/, "", k); v = $0; sub(/^  [a-z_0-9]+:/, "", v)
      printf "sel\t%s\t%s\n", k, unq(v); sub1 = ""; next
    }
    top == "sel" && /^  selected:[ \t]*$/ { sub1 = "selected"; next }
    top == "sel" && /^  declined:[ \t]*$/ { sub1 = "declined"; next }
    top == "sel" && sub1 == "selected" && /^    - [^ ]/ {
      v = $0; sub(/^    - /, "", v); printf "sel\tselected\t%s\n", unq(v); next
    }
    top == "sel" && sub1 == "declined" && /^    - name:/ {
      if (dname != "") { err("declined entry " dname " has no reason") }
      v = $0; sub(/^    - name:/, "", v); dname = unq(v); next
    }
    top == "sel" && sub1 == "declined" && /^      reason:/ {
      if (dname == "") { err("reason without a declined name"); next }
      v = $0; sub(/^      reason:/, "", v); printf "sel\tdeclined\t%s\t%s\n", dname, unq(v); dname = ""; next
    }
    top == "spec" && /^  - challenge:/ {
      i++; v = $0; sub(/^  - challenge:/, "", v); printf "spec\t%d\tchallenge\t%s\n", i, unq(v); next
    }
    top == "spec" && i > 0 && /^    (spec_digest|approver|by|date):/ {
      k = $1; sub(/:$/, "", k); v = $0; sub(/^    [a-z_]+:/, "", v)
      printf "spec\t%d\t%s\t%s\n", i, k, unq(v); next
    }
    { err("unexpected line: " $0) }
    END {
      if (dname != "") err("declined entry " dname " has no reason")
      if (nsel > 1) err("more than one selection: block")
      if (nspec > 1) err("more than one specification: block")
      exit bad
    }
  ' "$1"
}

insubset_candidates() {
  local file="$1"
  if [ "${2:-}" = --with-derived ]; then
    grep -v '^#' "$file" | awk -F'\t' '$7 == "in-subset" { print $1 "\t" $6 }' | LC_ALL=C sort
  else
    grep -v '^#' "$file" | awk -F'\t' '$7 == "in-subset" { print $1 }' | LC_ALL=C sort -u
  fi
}

imported_defs() {
  local rel="$1" ex imp f root
  ex="$(approval_digests_ex "${2:-}")"
  lean_imports "$ex/$rel" | while IFS= read -r imp; do
    for root in lean aeneas; do
      f="$root/${imp//.//}.lean"
      [ -f "$ex/$f" ] && echo "$f"
    done
  done
}
