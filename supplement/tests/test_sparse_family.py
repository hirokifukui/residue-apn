# test_sparse_family.py (R05c): Theorem sparse for every admissible c at m = 5, 7 (symbolic invariants:
# (H), mu = 0, Z empty, rho = B_c^{-1}(1) != 1) and the counts |C_m| = 15, 42 for m = 5, 7.
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rep_family'))
from sym import *
expect = {5: 15, 7: 42}
bad = 0
for m in (5, 7):
    F = GF(m); n = 0
    for c in range(2, F.q):
        A = {}
        for i in (-2, -1, 0, 1):
            A[i % m] = A.get(i % m, 0) ^ 1
        A[2 % m] = A.get(2 % m, 0) ^ c
        if not lin_invertible(F, A):
            continue
        n += 1
        cf, l = expand_LA3(F, A, {0: 1})
        iv = invariants(F, cf, l)
        if not (iv['H'] and iv['mu'] == 0 and iv['z'] == 0 and iv['rho'] != 1):
            bad += 1; print("FAIL", m, c, iv)
    print("m", m, "admissible", n, "expected", expect[m])
    bad += (n != expect[m])
if bad: print("SPARSE_FAMILY FAIL"); sys.exit(1)
print("SPARSE_FAMILY OK")
