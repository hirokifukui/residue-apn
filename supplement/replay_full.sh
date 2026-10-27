#!/bin/sh
# replay_full.sh (R04-13): FULL replay = core + m=7 complete exceptional rows + m=9 search + m=11/13 invariants.
# Runtime on a 2-core container: about 1-1.5 h. Memory: k=4, m=7 needs ~1.1 GB. Fail-fast as in replay_core.sh.
# R05c: validate_v3.py's per-run timeout is VTIMEOUT seconds (default 5400; was a fixed 1800, which the m=7, k=4
# sample of F1 exceeded on a slower container).
set -eu
cd "$(dirname "$0")"
STAGES="0 1 2 3 4 5 6 7 8 9" sh replay_core.sh
log() { echo "[full] $*"; }
rm -f layers/r05c/ver3_replay.jsonl layers/r05c/ver3_replay.log rep_sparse/replay_counts.out validate_v3_rep7.* validate_v3_P73_full.* validate_v3_P75.* rep/m9_search.log inv_P113nat.json inv_P113sp.json inv_P133nat.json inv_P133sp.json
log "F1 m=7 mu=0,Z empty representative: all 16384 exceptional rows (k=3) + k=4 samples (~30 min)"
VM=7 VK=3,4 VOUT=validate_v3_rep7.json VEXPECT_MATCH=2 VEXPECT_BOUND=0 python3 validate_v3.py rep7_nat.txt > validate_v3_rep7.out
tail -1 validate_v3_rep7.out
log "F2 P73sp / P73nat: all 16384 exceptional rows (k=3)"
VM=7 VK=3 VOUT=validate_v3_P73_full.json VEXPECT_MATCH=2 VEXPECT_BOUND=0 python3 validate_v3.py P73sp.txt P73nat.txt > validate_v3_P73_full.out
tail -1 validate_v3_P73_full.out
log "F3 P75sp / P75nat (r=5 family, +2X^3): all 16384 exceptional rows (k=3)"
VM=7 VK=3 VOUT=validate_v3_P75.json VEXPECT_MATCH=1 VEXPECT_BOUND=1 python3 validate_v3.py P75sp.txt P75nat.txt > validate_v3_P75.out
tail -1 validate_v3_P75.out
log "F3b Corollary natural: P75nat all rows + P95/P97 samples"
NATURAL_REQUIRE_P75=1 python3 tests/test_natural_k3.py > tests/natural_k3_full.out
tail -1 tests/natural_k3_full.out
log "F4 representative search m=9 (seed 20261025, 3e6 tries)"
rep/rsearch 9 20261025 3000000 > rep/m9_search.log
tail -1 rep/m9_search.log
log "F5 invariants of P_{11,3}, P_{13,3} natural and sparse lifts"
for f in P113nat P113sp; do python3 inv.py 11 $f.txt > inv_$f.json; done
for f in P133nat P133sp; do python3 inv.py 13 $f.txt > inv_$f.json; done
log "F6 intermediate layers (R05c): sub-case 3 lifts re-verified against exhaustive spectra; stored tables re-summarised"
(cd layers/r05c && gcc -O3 -o clsspec2 clsspec2.c && python3 verify_batch.py gen3.jsonl ver3_replay.jsonl > ver3_replay.log)
python3 tests/check_layers_r05c.py
log "F7 sparse family (R05c): |C_m| for m=5..13 and the curve count over F_(2^17)"
(cd rep_sparse && gcc -O2 -o pcount independent_param_count.c && gcc -O2 -o ccount independent_curve_count.c \
  && ./pcount 5 0x25 && ./pcount 7 0x83 && ./pcount 9 0x211 && ./pcount 11 0x805 && ./pcount 13 0x201b \
  && ./ccount 17 0x20009) > rep_sparse/replay_counts.out
python3 tests/check_sparse_counts.py
log "FULL REPLAY OK"
