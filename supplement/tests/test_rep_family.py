# R05b (Claude): Theorem repfamily (paper Section 10). For A_d = T_m + d X^{2^{m-2}} and p_d = A_d^3 (reduced),
# (H) holds with rho = d^{-4}, mu = 0, Z empty iff Tr d = Tr d^{-1} = 0. Two independent checks for m = 5, 7, 9:
# (a) rep_family/symcheck.py (symbolic invariants, every d), (b) rep_family/brute.c (function-level evaluation at
# every point, interpolation re-check, 2-to-1 derivative, rho, mu, Lambda at all points; full DDT for APN).
# Expected numbers of admissible d: N(5) = 10, N(7) = 28, N(9) = 126.
import os, sys, json, subprocess
here = os.path.dirname(os.path.abspath(__file__)); root = os.path.dirname(here); os.chdir(os.path.join(root, 'rep_family'))
N = {5: 10, 7: 28, 9: 126}; POLY = {5: 37, 7: 131, 9: 529}
out = subprocess.run([sys.executable, 'symcheck.py', 'all', '5,7,9'], capture_output=True, text=True, check=True).stdout
sym = [json.loads(l) for l in out.splitlines() if l.startswith('{')]
assert len(sym) == 3, out
for s in sym:
    assert s['tested'] == s['agree'] == (1 << s['m']) - 1 and s['hits'] == N[s['m']], s
subprocess.run(['gcc', '-O2', '-o', 'brute', 'brute.c'], check=True)
res = []
for m in (5, 7, 9):
    o = subprocess.run(['./brute', str(m), str(POLY[m]), 'all', '1'], capture_output=True, text=True, check=True).stdout
    summ = [l for l in o.splitlines() if l.startswith('SUMMARY')]
    assert summ, o[-500:]
    j = json.loads(summ[-1][len('SUMMARY '):])
    assert j['tested'] == j['agree_with_theorem'] == (1 << m) - 1 and j['hits'] == N[m], j
    res.append(j)
os.remove('brute')
json.dump(dict(symbolic=sym, brute=res), open(os.path.join(root, 'tests', 'rep_family.json'), 'w'), indent=1)
print('REP_FAMILY OK', [N[m] for m in (5, 7, 9)])
