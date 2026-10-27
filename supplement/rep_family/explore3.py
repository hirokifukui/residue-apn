import sys, itertools, random
sys.path.insert(0, '.')
from sym import *
m = int(sys.argv[1]); F = GF(m)
# exhaustive over A = x + a x^(2^(m-2)) + b x^(2^(m-1)), L = identity
from collections import Counter
cnt = Counter()
for a in range(1, F.q):
    for b in range(1, F.q):
        A = {0: 1, m-2: a, m-1: b}
        if not lin_invertible(F, A): continue
        iv = invariants(F, *expand_LA3(F, A, {0: 1}))
        if not iv['H']: cnt['noH:'+iv['why']] += 1; continue
        cnt[('mu0' if iv['mu']==0 else 'mu1', iv['z'])] += 1
print(m, dict(cnt))
