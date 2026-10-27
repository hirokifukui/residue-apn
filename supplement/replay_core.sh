#!/bin/sh
# replay_core.sh (R04-05/13, R05-04, R06: + tests/test_hull_layer.py): CORE replay. m=5 rings, symbolic certificates, regression tests and the m=7
# representative search. NOT the full replay (m=7 complete exceptional rows: replay_full.sh).
# Requirements: gcc, python3 (>=3.10), sympy, numpy (tests/test_crypto_c3.py).
# Fail-fast discipline (R04): every required command is its own statement under `set -eu`; no `cmd && next`
# guards; generated outputs are deleted before they are regenerated; regenerated representative tables are
# checked against pinned SHA-256 values. STAGES="1 2 ..." runs selected stages only (used by the negative controls).
set -eu
cd "$(dirname "$0")"
log() { echo "[core] $*"; }
STAGES="${STAGES-0 1 2 3 4 5 6 7 8 9}"
# A partial replay is not a core replay; reject empty and unknown scopes.
set -- $STAGES
if [ "$#" -eq 0 ]; then echo "[core] empty STAGES" >&2; exit 2; fi
seen=" "
for stage in "$@"; do
  case "$stage" in 0|1|2|3|4|5|6|7|8|9) ;; *) echo "[core] invalid stage: $stage" >&2; exit 2 ;; esac
  case "$seen" in *" $stage "*) echo "[core] duplicate stage: $stage" >&2; exit 2 ;; esac
  seen="$seen$stage "
done
STAGES="$*"
if [ "$STAGES" = "0" ]; then echo "[core] cleanup alone is not verification" >&2; exit 2; fi
if [ "$#" -eq 10 ]; then REPLAY_STATUS="CORE REPLAY OK"; else REPLAY_STATUS="PARTIAL REPLAY OK"; fi
want() { case " $STAGES " in *" $1 "*) return 0 ;; esac; return 1; }
sha_ok() {  # file expected-sha
  got=$(python3 -c "import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],'rb').read()).hexdigest())" "$1")
  if [ "$got" != "$2" ]; then echo "[core] SHA MISMATCH $1: $got != $2" >&2; exit 4; fi
}
log "tools: $(gcc --version | head -1) | $(python3 --version) | sympy $(python3 -c 'import sympy;print(sympy.__version__)')"
gcc -O3 -march=native -o grddt3 grddt3.c
gcc -O2 -o rep/rsearch rep/rsearch.c
if want 0; then
  log "0 clean generated outputs"
  rm -f cert/identities_cert.out e_tests.out e_tests.json negative_controls.out negative_controls.json
  rm -f validate_v3*.json validate_v3*.out rep/m5_search.log rep/m7_search.log rep/build_rep.out
  rm -f rep/representative_certificate.json rep/rep5_nat.txt rep/rep5_A1.txt rep/rep7_nat.txt rep/rep7_A1.txt
  rm -f rep5_nat.txt rep5_A1.txt rep7_nat.txt rep7_A1.txt tests/cross_level_regression.json tests/crypto_c3_test.json
  rm -f tests/markov_two_words.json tests/markov_two_words.out tests/natural_k3.json tests/natural_k3.out tests/rep_family.json tests/rep_family.out tests/m3_no_H_check.out tests/sparse_family.out tests/hull_toy.out tests/hull_layer.out cert/sparse_cert_r06.out
fi
if want 1; then
  log "1 symbolic identities (dimension-free)"
  cd cert
  python3 identities_cert.py > identities_cert.out
  cd ..
  tail -1 cert/identities_cert.out
fi
if want 2; then
  log "2 E-invariant positive/negative tests"
  python3 e_tests.py > e_tests.out
  tail -1 e_tests.out
fi
if want 3; then
  log "3 validate_v3 negative controls (8 checker faults + 9 scope faults + 2 positives)"
  python3 run_negative.py > negative_controls.out
  tail -1 negative_controls.out
fi
if want 4; then
  log "4 validate_v3: 12 m=5 inputs (k=3 all exceptional rows, k=4 samples)"
  VOUT=validate_v3.json VEXPECT_MATCH=23 VEXPECT_BOUND=1 python3 validate_v3.py F1_c0A1_plus2X2.txt P53nat.txt P53nat_split.txt P53sp.txt c0_A1.txt c0_A1_split.txt c1_A1.txt c1nat.txt m124_A1.txt m40_A1.txt m57_A1.txt m75_A1.txt > validate_v3.out
  tail -1 validate_v3.out
fi
if want 5; then
  log "5 validate_v3: (O3) inputs with A==0"
  VOUT=validate_v3_Azero.json VEXPECT_MATCH=2 VEXPECT_BOUND=2 python3 validate_v3.py c0_o3.txt c1_o3.txt > validate_v3_Azero.out
  tail -1 validate_v3_Azero.out
fi
if want 6; then
  log "6 representative search m=5 (trial) and m=7 (seed 20261025, 2e6 tries)"
  rep/rsearch 5 101 3000 > rep/m5_search.log
  rep/rsearch 7 20261025 2000000 > rep/m7_search.log
fi
if want 7; then
  log "7 representative certificate (m=5 from rep/rep5_seed.json; m=7 first mu=0,z=0 hit)"
  test -s rep/rep5_seed.json
  test -s rep/m7_search.log
  cd rep
  python3 build_rep.py > build_rep.out
  cd ..
  sha_ok rep/rep5_nat.txt 30846bc56fa371520d3b1ccb6d7c0dabf253ea55778ec9d55a0de8aac0127553
  sha_ok rep/rep5_A1.txt 42165da39f56cba0072e7675c33506638f74bb9345ee923c4ebe1c532de08751
  sha_ok rep/rep7_nat.txt 55347484e9bc507a1984234c5a2ac2feebb13cad5a9a2c41098b581f20eb84f0
  sha_ok rep/rep7_A1.txt 4a8fb674f30045646abc721d7806eddb8e63ccc97c7af5e72791806173e828af
  cp rep/rep5_nat.txt rep/rep5_A1.txt rep/rep7_nat.txt rep/rep7_A1.txt .
fi
if want 8; then
  log "8 validate_v3: rep5_nat, rep5_A1"
  VOUT=validate_v3_rep5.json VEXPECT_MATCH=2 VEXPECT_BOUND=2 python3 validate_v3.py rep5_nat.txt rep5_A1.txt > validate_v3_rep5.out
  tail -1 validate_v3_rep5.out
fi
if want 9; then
  log "9 regression tests: cross-level counterexample (R04-01), probability model (R04-03), two-word normalization (R05-01), natural lift and mu=0/Z empty family (R05b), sparse family and two-round differentials (R05c)"
  python3 tests/test_cross_level.py > tests/cross_level_regression.out
  tail -1 tests/cross_level_regression.out
  python3 tests/test_crypto_c3.py > tests/crypto_c3_test.out
  tail -1 tests/crypto_c3_test.out
  python3 tests/test_markov_two_words.py > tests/markov_two_words.out
  tail -1 tests/markov_two_words.out
  python3 tests/test_natural_k3.py > tests/natural_k3.out
  tail -1 tests/natural_k3.out
  python3 tests/test_rep_family.py > tests/rep_family.out
  tail -1 tests/rep_family.out
  python3 tests/m3_no_H_check.py > tests/m3_no_H_check.out
  tail -1 tests/m3_no_H_check.out
  python3 tests/test_sparse_family.py > tests/sparse_family.out
  tail -1 tests/sparse_family.out
  python3 tests/test_hull_toy.py > tests/hull_toy.out
  tail -1 tests/hull_toy.out
  python3 tests/test_hull_layer.py > tests/hull_layer.out
  tail -1 tests/hull_layer.out
  python3 cert/sparse_cert_r06.py > cert/sparse_cert_r06.out
  tail -1 cert/sparse_cert_r06.out
fi
log "$REPLAY_STATUS (stages: $STAGES)"
