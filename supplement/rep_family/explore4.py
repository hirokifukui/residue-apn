import sys
sys.path.insert(0, '.')
from sym import *
from collections import Counter
m = int(sys.argv[1]); F = GF(m)
cnt = Counter(); ex=[]
for c in range(2, F.q):
    A = {0: 1, 1: 1, m-2: c, m-1: 1}
    if not lin_invertible(F, A): cnt['noninv'] += 1; continue
    iv = invariants(F, *expand_LA3(F, A, {0: 1}))
    if not iv['H']: cnt['noH:'+iv['why']] += 1; continue
    cnt[('mu0' if iv['mu']==0 else 'mu1', iv['z'], 'Trc=%d'%F.tr(c))] += 1
    if iv['mu']==0 and iv['z']==0 and len(ex)<3: ex.append(c)
print(m, dict(cnt), ex)
