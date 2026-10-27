import sys
sys.path.insert(0, '.')
from sym import *
from collections import Counter
for m in (5,7,9,11):
    F = GF(m); cnt = Counter()
    for d in range(1, F.q):
        A = {i: 1 for i in range(m)}; A[m-2] ^= d
        cls = (F.tr(d), F.tr(F.inv(d)))
        if not lin_invertible(F, A): cnt[(cls,'noninv')] += 1; continue
        iv = invariants(F, *expand_LA3(F, A, {0: 1}))
        if not iv['H']: cnt[(cls,'noH')] += 1; continue
        cnt[(cls, iv['mu']==0, iv['z'], iv['rho']==F.pow(F.inv(d),4))] += 1
    print(m, dict(cnt))
