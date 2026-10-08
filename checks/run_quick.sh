#!/bin/bash
# run_quick.sh -- R5 main paper: every check of the main line from the files of this folder alone (Claude, 2026-10-06).
#   bash run_quick.sh           (about 10 min on one core; Python 3 + NumPy)
# Detach: (nohup bash run_quick.sh > /dev/null 2>&1 < /dev/null &)
# Steps: verify src/ against MANIFEST_SRC.sha256 (a missing or changed file stops the run, exit 2); copy src/ into a new
# repro_runs/<timestamp>/; run each step; every log ends with exit=<code>; STATUS ends with OVERALL PASS/FAIL.
# Exit status: 0 iff the sources verify, every step exits 0 and check_claims_main.py finds every stated value.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE" || exit 2
if command -v sha256sum >/dev/null; then SHA="sha256sum"; else SHA="shasum -a 256"; fi
$SHA -c MANIFEST_SRC.sha256 > /dev/null 2>&1 || { echo "source verification FAILED (missing or modified file under src/)"; $SHA -c MANIFEST_SRC.sha256 2>&1 | grep -v ': OK$'; exit 2; }
RUN="$HERE/repro_runs/$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RUN" && cp src/*.py "$RUN"/ && cd "$RUN" || exit 2
export PYTHONDONTWRITEBYTECODE=1
$SHA *.py > SOURCES.sha256
FAIL=0; : > STATUS
step () { name=$1; shift; "$@" > "$name.log" 2>&1; ec=$?; echo "exit=$ec" >> "$name.log"; echo "$name exit=$ec" >> STATUS; [ $ec -eq 0 ] || FAIL=1; }
step S1 python3 r3_checks.py S1
step S2 python3 r3_checks.py S2 16
step S3 python3 r3_checks.py S3
step thmA python3 thmA.py
step ring python3 ring.py
for c in C1 C2 C3; do step $c python3 main_checks.py $c; done
step C4 python3 controls_R6.py
step check_claims python3 check_claims_main.py
echo "OVERALL $([ $FAIL -eq 0 ] && echo PASS || echo FAIL)" >> STATUS
cat STATUS
exit $FAIL
