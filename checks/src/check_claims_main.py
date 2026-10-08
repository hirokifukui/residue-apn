"""check_claims_main.py -- compares the logs of run_quick.sh with the values stated in manuscript.tex (Claude, 2026-10-06).
Run inside a run directory. Exit 0 iff every stated value is found."""
import sys; sys.dont_write_bytecode = True
import ast, json, re
FAILS = []; RES = []
def check(cid, cond, msg):
    RES.append([cid, bool(cond), msg]); print(('PASS ' if cond else 'FAIL ') + cid + ' ' + msg)
    if not cond: FAILS.append(cid)
def read(f):
    try: return open(f).read()
    except OSError: return ''
t = read('thmA.log')
check('T-A', 'formula pairs 1003 bad 0' in t, 'thmA.py: 1003 admissible pairs m<=101, 3r-2 terms, deg 3q/4, P\' = 1+W+Y, no bad pair')
recs = [ast.literal_eval(l) for l in t.splitlines() if l.startswith('{')]
from math import gcd
adm = [r for r in recs if gcd(r['r'], r['m']) == 1]; neg = [r for r in recs if gcd(r['r'], r['m']) != 1]
check('T-A', adm and all(r['eq'] and r['perm'] and r['maxDDT'] == 2 and r['opt'] and r['d1_is_tr1'] for r in adm),
      'thmA.py: field checks m=5..13, %d admissible (m,r): composition = polynomial, permutation, DU 2, derivative-optimal, {P(y+1)+P(y)} = {Tr=1}' % len(adm))
check('T-A', neg and all(not r['perm'] for r in neg), 'thmA.py negative control (m,r)=(9,3), gcd 3: not a permutation')
rg = read('ring.log')
check('T-R', "k 2 {'P53': {'perm': True, 'G': {2: 960}, 'X': {64: 32}, 'Z': {64: 31}}" in rg, 'ring.py k=2: natural lift of P_{5,3}: perm, unit rows <=2, rows over rho max 64, residue-zero rows 64')
check('T-R', "k 3 {'P53': {'perm': True, 'G': {2: 30720}, 'X': {128: 1024}, 'Z': {1024: 480, 2048: 543}}" in rg, 'ring.py k=3: rows over rho max 128, residue-zero rows max 2048 = 2q^2')
for s, needles in (('S1', ['PASS S1 Stone', 'PASS S1 TIT P_{e,t}']), ('S2', ['PASS S2 Theorem A support', 'PASS S2 Theorem B: E == 1+T_r', 'PASS S2 Riemann-Hurwitz']),
                   ('S3', ['PASS S3 Lemma P m=13', 'PASS S3 cyclotomic classes'])):
    L = read(s + '.log')
    check('r3_' + s, all(n in L for n in needles) and 'FAIL' not in L, 'r3_checks %s: %s' % (s, '; '.join(needles)))
for c, needles in (('C1', ['PASS C1 (X^4+X^2+1)(X^2+1) = X^6+1', 'PASS C1 e=1:', 'PASS C1 e=6:']),
                   ('C2', ['PASS C2 natural k=2', 'PASS C2 random_lift k=2', 'PASS C2 natural k=3', 'PASS C2 random_lift k=3']),
                   ('C3', ['PASS C3 m=5: all 210', 'PASS C3 m=7: all 3906', 'control'])):
    L = read(c + '.log')
    check('main_' + c, all(n in L for n in needles) and 'FAIL' not in L, 'main_checks %s' % c)
L = read('C4.log')
check('main_C4', all(n in L for n in ['PASS C4a reviewer pair: codes 6 and 15 both map to 100', 'PASS C4a family member P_{7,5} permutes F_128',
      "PASS C4b e=3 gcd(e,9)=3: {'gcd': 3, 'perm': True, 'DU': 8, 'derivative_zeros': 0, 'fibre_sizes': [8]", 'PASS C4b e=4: 16 roots of g_e, 8 finite branch values',
      'PASS C4c binary-word lemma: 928 pairs']) and 'FAIL' not in L, 'controls_R6 C4: fixed P_{5,3} not a permutation of F_128; Rem 4.2 gcd control m=9; binary-word lemma')
json.dump(RES, open('claims_result.json', 'w'), indent=1)
sys.exit(1 if FAILS else 0)
