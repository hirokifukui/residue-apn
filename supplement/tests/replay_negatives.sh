#!/bin/sh
# R04-05 negative controls for replay_core.sh. Each case runs on a fresh copy of the clean tree; a case passes
# iff the replay exits non-zero AND never prints "REPLAY OK". Positive control: stage 1 must succeed with
# "PARTIAL REPLAY OK" (R05: a partial run is never reported as a core replay).
# Usage: sh tests/replay_negatives.sh <m7_search.log from a completed core replay>
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
M7LOG=$1
test -s "$M7LOG" || { echo "need a m7_search.log"; exit 2; }
fresh() { d=$(mktemp -d); cp -r "$ROOT/." "$d/"; rm -f "$d"/rep5_*.txt "$d"/rep7_*.txt "$d"/rep/rep5_nat.txt "$d"/rep/rep5_A1.txt "$d"/rep/rep7_*.txt; echo "$d"; }
fail=0; n=0
check() {  # name dir expect(neg|pos) env-assignments...
  name=$1; d=$2; exp=$3; shift 3
  out=$(cd "$d" && env "$@" sh replay_core.sh 2>&1); rc=$?
  ok=0; echo "$out" | grep -q "REPLAY OK" && ok=1
  if [ "$exp" = neg ]; then
    if [ $rc -ne 0 ] && [ $ok -eq 0 ]; then res=PASS; else res=FAIL; fail=$((fail+1)); fi
  else
    if [ $rc -eq 0 ] && echo "$out" | grep -q "PARTIAL REPLAY OK" && ! echo "$out" | grep -q "CORE REPLAY OK"; then res=PASS; else res=FAIL; fail=$((fail+1)); fi
  fi
  n=$((n+1)); echo "$res $name exit=$rc replay_ok_printed=$ok last=[$(echo "$out" | tail -1)]"
}
# N1 seed missing
d=$(fresh); rm -f "$d/rep/rep5_seed.json"; cp "$M7LOG" "$d/rep/m7_search.log"
check seed_missing "$d" neg STAGES=7
# N2 representative generator exits 7
d=$(fresh); printf 'import sys\nsys.exit(7)\n' > "$d/rep/build_rep.py"; cp "$M7LOG" "$d/rep/m7_search.log"
check generator_exit7 "$d" neg STAGES=7
# N3 stale outputs + generator that writes nothing and exits 0
d=$(fresh); printf 'print("noop")\n' > "$d/rep/build_rep.py"; cp "$M7LOG" "$d/rep/m7_search.log"
for f in rep5_nat rep5_A1 rep7_nat rep7_A1; do cp "$d/c0_A1.txt" "$d/rep/$f.txt"; cp "$d/c0_A1.txt" "$d/$f.txt"; done
check stale_outputs_kept "$d" neg STAGES=7
# N4 stale outputs, clean stage first, generator writes nothing
d=$(fresh); printf 'print("noop")\n' > "$d/rep/build_rep.py"; cp "$M7LOG" "$d/rep/m7_search.log"
for f in rep5_nat rep5_A1 rep7_nat rep7_A1; do cp "$d/c0_A1.txt" "$d/rep/$f.txt"; done
check stale_outputs_cleaned "$d" neg "STAGES=0 7"
# N5 m7 search log missing
d=$(fresh); rm -f "$d/rep/m7_search.log"
check m7_log_missing "$d" neg STAGES=7
# N6 row checker exits 7 inside the main validation stage
d=$(fresh); (cd "$d" && sh neg/mk.sh)
check checker_exit7_stage4 "$d" neg STAGES=4 GRDDT="$d/neg/exit7.sh"
# N7 a tampered representative table (one coefficient changed) -> SHA mismatch
d=$(fresh); cp "$M7LOG" "$d/rep/m7_search.log"
printf 'import runpy,sys\nsys.argv=["build_rep.py"]\nrunpy.run_path("build_rep_real.py",run_name="__main__")\nL=open("rep5_A1.txt").read().splitlines()\nL[1]=L[1][:-1]+("1" if L[1][-1]!="1" else "2")\nopen("rep5_A1.txt","w").write("\\n".join(L)+"\\n")\n' > "$d/rep/build_rep_wrap.py"
mv "$d/rep/build_rep.py" "$d/rep/build_rep_real.py"; mv "$d/rep/build_rep_wrap.py" "$d/rep/build_rep.py"
check tampered_table "$d" neg STAGES=7
# P1 positive control
d=$(fresh)
check positive_stage1 "$d" pos STAGES=1
echo "REPLAY_NEGATIVES: $n cases, $fail failures"
[ $fail -eq 0 ] && echo "REPLAY_NEGATIVES OK" || exit 1
