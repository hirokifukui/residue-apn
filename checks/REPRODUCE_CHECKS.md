# Finite checks — steps, claims and scope

Scope: finite calibrations of the general identities on stated parameter ranges, recomputations of the finite tables
quoted in the paper, and negative controls. They do not prove the general statements (the proofs are in the paper,
and the Lean-formalized parts are listed in `../TRUST.md`) and they do not parse the manuscript;
`check_claims_main.py` holds the stated values by hand.

## Requirements
Python 3 with NumPy. Nothing outside this folder is read.

## One command
```
bash run_quick.sh            # about 6–10 minutes, one core
python3 compare_expected.py repro_runs/<timestamp>     # compares STATUS and the 8 JSON outputs with expected/
```
1. `MANIFEST_SRC.sha256` is checked first; a missing or modified file under `src/` stops the run with exit 2.
2. A new folder `repro_runs/<timestamp>/` receives copies of `src/*.py` and `SOURCES.sha256`; nothing else is written.
3. Each step log ends with `exit=<code>`; `STATUS` ends with `OVERALL PASS` or `OVERALL FAIL`.
4. Exit status 0 iff the sources verify, every step exits 0 and `check_claims_main.py` finds every stated value.

## Steps
| step | script | claims (`CLAIM_STATUS.tsv` id) |
|---|---|---|
| S1 | `r3_checks.py S1` | P_{5,3} = Stone's example; P_{e,t} branch values, e = 2..6 (R-tit) |
| S2 | `r3_checks.py S2 16` | T-A, P-C, T-B: sparse identities for all admissible (m,r), m ≤ 101; gcd(g,E), s ≤ 16; g-adic order m ≤ 11; field checks m ≤ 13; Riemann–Hurwitz |
| S3 | `r3_checks.py S3` | L-LW: criterion, kernel dimension m, cyclotomic classes m ≤ 61 |
| thmA | `thmA.py` | T-A: 1003 admissible pairs m ≤ 101; field checks m = 5..13; negative control (m,r) = (9,3) |
| ring | `ring.py` | P-lift, T-R: natural lift of P_{5,3}, GR(4,5) and GR(8,5), all directions |
| C1 | `main_checks.py C1` | R-tit: e = 1 factorisation; exactly 2^{e−1} values, e = 1..6 |
| C2 | `main_checks.py C2` | P-lift, T-R, R-RS: natural and one random coefficient lift, k = 2, 3, full tables |
| C3 | `main_checks.py C3` | P-W: m = 5, 7, every admissible (a,b); control with random invertible matrices |
| C4 | `controls_R6.py` | T-A: fixed P_{5,3} is not a permutation of F_128, P_{7,3}, P_{7,5} are; R-tit: m = 9, e = 3 (gcd 3) permutation with DU 8 and fibres 8, e = 1, 2, 4 optimal APN; 2^(e−1) branch values e = 1..4; L-LW: binary-word lemma, odd m ≤ 61, all 1 ≤ k < m |
| check_claims | `check_claims_main.py` | compares the logs with the stated values |

## Expected output
`expected/` holds `STATUS` and the 8 JSON outputs of the reference run named in `expected/SOURCE_RUN` (same `src/`
as `MANIFEST_SRC.sha256`). An independent reviewer re-ran these 10 steps in another environment and obtained the
same 8 JSON files (internal review, not peer review).
