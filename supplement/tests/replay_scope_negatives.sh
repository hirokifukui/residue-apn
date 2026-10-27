#!/bin/sh
# R05-04 scope controls for replay_core.sh and rep/m11check.py (GPT R04b review M4).
# STAGES must be a non-empty set of distinct stages from 0..9; cleanup alone is not verification; a partial run
# prints "PARTIAL REPLAY OK", never "CORE REPLAY OK". m11check must exit non-zero on an empty witness list and on
# a witness whose recomputed invariants disagree. All cases run on fresh copies of the tree.
# Usage: sh tests/replay_scope_negatives.sh
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
fresh() { d=$(mktemp -d); cp -r "$ROOT/." "$d/"; echo "$d"; }
fail=0; n=0
report() { n=$((n+1)); if [ "$1" = PASS ]; then :; else fail=$((fail+1)); fi; echo "$1 $2 exit=$3 last=[$4]"; }
stage_neg() {  # name stages
  d=$(fresh); out=$(cd "$d" && STAGES="$2" sh replay_core.sh 2>&1); rc=$?
  if [ $rc -ne 0 ] && ! echo "$out" | grep -q "REPLAY OK"; then r=PASS; else r=FAIL; fi
  report $r "$1" $rc "$(echo "$out" | tail -1)"; rm -rf "$d"
}
stage_neg S1_unknown_99 "99"
stage_neg S2_blank "   "
stage_neg S3_empty ""
stage_neg S4_duplicate "1 1"
stage_neg S5_cleanup_only "0"
stage_neg S6_garbage_token "1 x"
stage_neg S7_out_of_range_10 "10"
stage_neg S8_negative "-1"
# P1 partial run is reported as partial
d=$(fresh); out=$(cd "$d" && STAGES="1" sh replay_core.sh 2>&1); rc=$?
if [ $rc -eq 0 ] && echo "$out" | grep -q "PARTIAL REPLAY OK" && ! echo "$out" | grep -q "CORE REPLAY OK"; then r=PASS; else r=FAIL; fi
report $r P1_partial_stage1 $rc "$(echo "$out" | tail -1)"; rm -rf "$d"
# M1 m11 witness list empty
d=$(fresh); printf 'DONE tries=0\n' > "$d/rep/m11_search.log"
out=$(cd "$d" && python3 rep/m11check.py 2>&1); rc=$?
if [ $rc -ne 0 ] && ! echo "$out" | grep -q "M11_CHECK OK"; then r=PASS; else r=FAIL; fi
report $r M1_m11_empty $rc "$(echo "$out" | tail -1)"; rm -rf "$d"
# M2 m11 witness whose recomputed mu disagrees
d=$(fresh); printf 'HIT rho=1 mu=0 z=0 coeffs=1:1\n' > "$d/rep/m11_search.log"
cat > "$d/inv.py" <<'PY'
print('{"rho":1,"mu":1,"Z":[],"A":[1]}')
PY
out=$(cd "$d" && python3 rep/m11check.py 2>&1); rc=$?
if [ $rc -ne 0 ] && echo "$out" | grep -q "M11_CHECK FAIL"; then r=PASS; else r=FAIL; fi
report $r M2_m11_mismatch $rc "$(echo "$out" | tail -1)"; rm -rf "$d"
# M3 m11 witness with wrong rho
d=$(fresh); printf 'HIT rho=2 mu=0 z=0 coeffs=1:1\n' > "$d/rep/m11_search.log"
cat > "$d/inv.py" <<'PY'
print('{"rho":1,"mu":0,"Z":[],"A":[1]}')
PY
out=$(cd "$d" && python3 rep/m11check.py 2>&1); rc=$?
if [ $rc -ne 0 ] && echo "$out" | grep -q "M11_CHECK FAIL"; then r=PASS; else r=FAIL; fi
report $r M3_m11_rho_mismatch $rc "$(echo "$out" | tail -1)"; rm -rf "$d"
echo "REPLAY_SCOPE: $n cases, $fail failures"
[ $fail -eq 0 ] && echo "REPLAY_SCOPE OK" || exit 1
