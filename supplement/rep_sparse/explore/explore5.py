# A_c = x + x^2 + c x^4 + c x^(2^(m-2)) + x^(2^(m-1)), p = A_c^3 ; expect rho=1, mu=0, Z=empty when Tr c=1, c!=1, A_c invertible
import sys
sys.path.insert(0, '.')
from sym import *
from collections import Counter
for m in map(int, sys.argv[1:]):
    F = GF(m); cnt = Counter(); good=[]
    for c in range(1, F.q):
        A = {0:1, 1:1, 2:c, m-2:c, m-1:1}
        inv = lin_invertible(F, A)
        key = ('Tr', F.tr(c), 'inv', inv)
        if inv:
            iv = invariants(F, *expand_LA3(F, A, {0:1}))
            key += (('H', iv['H']) + ((iv['rho'], iv['mu'], iv['z']) if iv['H'] else (iv['why'],)),)
            if iv['H'] and iv['mu']==0 and iv['z']==0: good.append(c)
        cnt[key] += 1
    print(m, dict(cnt), 'good', len(good), good[:10])
