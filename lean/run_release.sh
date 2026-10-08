#!/usr/bin/env bash
# run_release.sh -- fail-closed release check of the ResidueAPN Lean formalization (session R11; GPT R8-01).
#
# Exit 0 and write <logs>/PASS.json ONLY if every gate passes. The first failing gate stops the run with a nonzero
# exit (the failing command's own exit code where there is one), writes <logs>/FAIL.json and never PASS.json.
# Nothing is deleted: the log directory must be new or empty (otherwise the run refuses to start), so an old
# PASS.json can never be mistaken for a new one.
#
# Paths are resolved from the position of this script (no home directory and no sibling work tree is used):
#   <script dir>/residue_apn_portable/   Lean project (math sources, audit/, lakefile.toml, lake-manifest.json)
#   <script dir>/PINS.json               expected math-source digest, toolchain, Mathlib and lean4checker revisions
#   <script dir>/FINAL_DECLARATIONS.txt  declarations that must each have an axiom line in the audit output
#
# Gates, in order:
#   0 inputs     project, audit files, PINS.json, FINAL_DECLARATIONS.txt exist; lake, git (and the checker) exist
#   1 config     lean-toolchain and the Mathlib revision in lakefile.toml and lake-manifest.json equal PINS.json;
#                with --checker-rev-check, the checker's git checkout is at the pinned lean4checker revision
#   2 src_before math-source digest equals PINS.json math_source_digest
#   3 fetch      (only with --cache-get) lake exe cache get
#   4 build      lake build
#   5 audit      lake env lean <each audit file>
#   6 axioms     no sorryAx; every "depends on axioms" line lists a subset of {propext, Classical.choice, Quot.sound};
#                every name in FINAL_DECLARATIONS.txt has its own axiom line; no "does not depend on any axioms" is
#                required (such a line is allowed: the empty set is a subset)
#   7 checker    lake env <lean4checker> --fresh ResidueAPN.All   (one leaf module importing every part)
#   8 src_after  math-source digest unchanged
#
# Math-source digest rule (as recorded since stage 2): sha256 of the concatenated 64-hex sha256 values, one per line,
# of `LC_ALL=C sort` of ResidueAPN/**/*.lean followed by ResidueAPN.lean.
#
# Usage:
#   bash run_release.sh --checker <lean4checker binary> --logs <new or empty dir> [--cache-get] [--checker-rev-check]
# Bash 3.2 compatible (macOS /bin/bash). Each stage is a brace group whose status is that of its command (no pipes).
# errtrace (-E) is deliberately off: an ERR trap inherited by a command substitution would write FAIL.json from a
# subshell without stopping the main run (seen in the first test run, R11). PASS.json is also refused if FAIL.json exists.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT="$HERE/residue_apn_portable"
PINS="$HERE/PINS.json"
FINALS="$HERE/FINAL_DECLARATIONS.txt"
AUDITS="audit/AuditStage1.lean audit/AuditStage2.lean audit/AuditStage3.lean audit/AuditAxiomsAll.lean"
MODULE="ResidueAPN.All"
CHECKER=""; LOGS=""; CACHE_GET=0; REV_CHECK=0

while [ $# -gt 0 ]; do
  case "$1" in
    --checker) CHECKER="${2:-}"; shift 2;;
    --logs) LOGS="${2:-}"; shift 2;;
    --cache-get) CACHE_GET=1; shift;;
    --checker-rev-check) REV_CHECK=1; shift;;
    --project) PROJECT="${2:-}"; shift 2;;   # for tests on copies only
    *) echo "unknown argument: $1" >&2; exit 2;;
  esac
done
if [ -z "$CHECKER" ] || [ -z "$LOGS" ]; then
  echo "usage: run_release.sh --checker <lean4checker binary> --logs <new or empty dir> [--cache-get] [--checker-rev-check]" >&2
  exit 2
fi

if [ -e "$LOGS" ]; then
  if [ ! -d "$LOGS" ] || [ -n "$(ls -A "$LOGS")" ]; then
    echo "RELEASE_CHECK=FAIL stage=logs exit=2: log directory exists and is not empty: $LOGS (use a new directory)" >&2
    exit 2
  fi
fi
mkdir -p "$LOGS"
LOGS="$(cd "$LOGS" && pwd)"
: > "$LOGS/stages.tsv"

now() { date -u '+%Y-%m-%dT%H:%M:%SZ'; }
fail() {  # fail <stage> <code> <message>
  local stage="$1" code="$2" msg="$3"
  [ "$code" = "0" ] && code=1
  trap - ERR
  printf '{"result": "FAIL", "stage": "%s", "exit": %s, "message": "%s", "time": "%s"}\n' \
    "$stage" "$code" "$(printf '%s' "$msg" | tr '"\\' "''")" "$(now)" > "$LOGS/FAIL.json"
  echo "$stage FAIL $code" >> "$LOGS/stages.tsv"
  echo "RELEASE_CHECK=FAIL stage=$stage exit=$code: $msg" >&2
  exit "$code"
}
trap 'fail internal $? "unexpected error at line $LINENO"' ERR
ok() { echo "$1 0" >> "$LOGS/stages.tsv"; }

sha256() { if command -v shasum >/dev/null 2>&1; then shasum -a 256 "$@"; else sha256sum "$@"; fi; }
pin() { sed -n 's/.*"'"$1"'": *"\([^"]*\)".*/\1/p' "$PINS" | head -n 1; }

# ---- gate 0: inputs and commands
[ -d "$PROJECT" ] || fail inputs 3 "project directory not found: $PROJECT"
[ -f "$PINS" ] || fail inputs 3 "PINS.json not found next to the script"
[ -f "$FINALS" ] || fail inputs 3 "FINAL_DECLARATIONS.txt not found next to the script"
PROJECT="$(cd "$PROJECT" && pwd)"
for a in $AUDITS; do [ -f "$PROJECT/$a" ] || fail inputs 3 "audit file missing: $a"; done
[ -f "$PROJECT/ResidueAPN.lean" ] && [ -d "$PROJECT/ResidueAPN" ] || fail inputs 3 "math sources missing in $PROJECT"
command -v lake >/dev/null 2>&1 || fail inputs 127 "command not found: lake (install elan; it reads lean-toolchain)"
command -v git >/dev/null 2>&1 || fail inputs 127 "command not found: git"
case "$CHECKER" in /*) ;; *) CHECKER="$(pwd)/$CHECKER";; esac
[ -f "$CHECKER" ] && [ -x "$CHECKER" ] || fail inputs 127 "lean4checker binary not found or not executable: $CHECKER"
ok inputs

# ---- gate 1: configuration pins
EXP_SRC="$(pin math_source_digest)"; EXP_TC="$(pin lean_toolchain)"; EXP_ML="$(pin mathlib_rev)"; EXP_CK="$(pin lean4checker_rev)"
[ -n "$EXP_SRC" ] && [ -n "$EXP_TC" ] && [ -n "$EXP_ML" ] && [ -n "$EXP_CK" ] || fail config 4 "PINS.json lacks a required key"
cd "$PROJECT"
[ "$(cat lean-toolchain)" = "$EXP_TC" ] || fail config 5 "lean-toolchain is '$(cat lean-toolchain)', pinned '$EXP_TC'"
grep -q "rev = \"$EXP_ML\"" lakefile.toml || fail config 5 "lakefile.toml does not require mathlib at $EXP_ML"
grep -q "\"rev\": \"$EXP_ML\"" lake-manifest.json || fail config 5 "lake-manifest.json does not pin mathlib at $EXP_ML"
if grep -q '"type": "path"' lake-manifest.json; then fail config 5 "lake-manifest.json contains a path dependency"; fi
CK_REV="unknown"
CK_DIR="$(cd "$(dirname "$CHECKER")" && pwd)"
CK_TOP="$(git -C "$CK_DIR" rev-parse --show-toplevel 2>/dev/null || true)"
if [ -n "$CK_TOP" ]; then CK_REV="$(git -C "$CK_TOP" rev-parse HEAD 2>/dev/null || echo unknown)"; fi
if [ "$REV_CHECK" = "1" ] && [ "$CK_REV" != "$EXP_CK" ]; then fail config 5 "lean4checker revision $CK_REV != pinned $EXP_CK"; fi
{ echo "lean_toolchain_file $(cat lean-toolchain)"; lake --version 2>&1 || true; uname -a; echo "checker $CHECKER rev $CK_REV"; } > "$LOGS/toolchain.txt" 2>&1 || true
{ for f in lakefile.toml lean-toolchain lake-manifest.json $AUDITS; do sha256 "$f"; done; sha256 "$PINS" "$FINALS" "$HERE/run_release.sh"; } > "$LOGS/config_sha256.txt"
ok config

# ---- gate 2: math-source digest before
src_digest() {  # writes the listing to $1, prints the digest
  { LC_ALL=C find ResidueAPN -type f -name '*.lean' | LC_ALL=C sort | while IFS= read -r f; do sha256 "$f"; done; sha256 ResidueAPN.lean; } > "$1"
  cut -c1-64 "$1" | sha256 | cut -c1-64
}
SRC_BEFORE="$(src_digest "$LOGS/source_sha256_before.txt")" || fail src_before 4 "cannot hash sources"
NFILES="$(wc -l < "$LOGS/source_sha256_before.txt" | tr -d ' ')"
[ "$SRC_BEFORE" = "$EXP_SRC" ] || fail src_before 5 "math-source digest $SRC_BEFORE != pinned $EXP_SRC"
ok src_before

run_stage() {  # run_stage <name> <log> <command...>
  local name="$1" log="$2"; shift 2
  local rc=0
  { echo "# $(now) $name: $*"; "$@"; } > "$log" 2>&1 || rc=$?
  echo "# $(now) exit=$rc" >> "$log"
  [ "$rc" -eq 0 ] || fail "$name" "$rc" "command failed; see $(basename "$log")"
  ok "$name"
}

# ---- gates 3-5
ulimit -n 8192 2>/dev/null || true
if [ "$CACHE_GET" = "1" ]; then run_stage fetch "$LOGS/fetch.log" lake exe cache get; fi
run_stage build "$LOGS/build.log" lake build
if grep -q "declaration uses 'sorry'" "$LOGS/build.log"; then fail build 6 "the build log reports a declaration using sorry"; fi
: > "$LOGS/audit_all.log"
for a in $AUDITS; do
  n="$(basename "$a" .lean)"
  run_stage "audit_$n" "$LOGS/audit_$n.log" lake env lean "$a"
  cat "$LOGS/audit_$n.log" >> "$LOGS/audit_all.log"
done

# ---- gate 6: axioms
A="$LOGS/audit_all.log"
if grep -q 'sorryAx' "$A"; then fail axioms 6 "sorryAx occurs in the audit output"; fi
BAD="$(grep 'depends on axioms:' "$A" | sed -e 's/.*depends on axioms: \[//' -e 's/\][[:space:]]*$//' \
       | tr ',' '\n' | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' \
       | grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
[ -z "$BAD" ] || fail axioms 6 "non-allowed axioms: $(echo "$BAD" | sort -u | tr '\n' ' ')"
NFIN=0
while IFS= read -r d; do
  case "$d" in ''|'#'*) continue;; esac
  NFIN=$((NFIN + 1))
  grep -q -F "'$d' depends on axioms:" "$A" || grep -q -F "'$d' does not depend on any axioms" "$A" \
    || fail axioms 6 "no axiom line for $d"
done < "$FINALS"
[ "$NFIN" -gt 0 ] || fail axioms 6 "FINAL_DECLARATIONS.txt is empty"
NAX="$(grep -c 'depends on axioms:' "$A" || true)"
ok axioms

# ---- gate 7: kernel re-check of the whole closure (one leaf module)
run_stage checker "$LOGS/checker_fresh.log" lake env "$CHECKER" --fresh "$MODULE"

# ---- gate 8: math-source digest after
SRC_AFTER="$(src_digest "$LOGS/source_sha256_after.txt")" || fail src_after 4 "cannot hash sources"
[ "$SRC_AFTER" = "$SRC_BEFORE" ] || fail src_after 5 "sources changed during the run: $SRC_BEFORE -> $SRC_AFTER"
ok src_after

# ---- every gate passed: PASS.json last (temp name, then mv)
[ ! -e "$LOGS/FAIL.json" ] || fail final 9 "FAIL.json present although every gate returned 0"
[ "$(grep -c ' 0$' "$LOGS/stages.tsv")" = "$(wc -l < "$LOGS/stages.tsv" | tr -d ' ')" ] || fail final 9 "a stage line is not 0"
trap - ERR
cat > "$LOGS/PASS.json.partial" <<EOF
{
  "result": "PASS",
  "time": "$(now)",
  "host": "$(hostname)",
  "project": "$PROJECT",
  "math_source_digest": "$SRC_BEFORE",
  "math_source_files": $NFILES,
  "lean_toolchain": "$EXP_TC",
  "mathlib_rev": "$EXP_ML",
  "lean4checker_rev_observed": "$CK_REV",
  "module_checked_fresh": "$MODULE",
  "final_declarations": $NFIN,
  "axiom_lines": $NAX,
  "stages": "$(tr '\n' ';' < "$LOGS/stages.tsv")"
}
EOF
mv "$LOGS/PASS.json.partial" "$LOGS/PASS.json"
echo "RELEASE_CHECK=PASS math_source_digest=$SRC_BEFORE"
exit 0
