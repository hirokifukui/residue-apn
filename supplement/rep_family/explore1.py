import sys, itertools
sys.path.insert(0, '.')
from sym import *
m = int(sys.argv[1]); F = GF(m)
# A0: F2 coefficients, terms set; L = beta * L0  -> p = L0(beta*A0^3)?  we use L = {k: beta^(2^k)} on support of L0
res = {}
supports = [s for r in (1, 2, 3) for s in itertools.combinations(range(m), r)]
Asup = [s for s in supports if len(s) == 3]
Lsup = [s for s in supports if len(s) <= 2]
for As in Asup:
    A = {k: 1 for k in As}
    if not lin_invertible(F, A): continue
    for Ls in Lsup:
        hits = 0; Hs = 0
        for beta in range(1, F.q):
            L = {k: F.frob(beta, k) for k in Ls}
            if not lin_invertible(F, L): continue
            c, l = expand_LA3(F, A, L)
            iv = invariants(F, c, l)
            if iv['H']:
                Hs += 1
                if iv['mu'] == 0 and iv['z'] == 0: hits += 1
        if hits: print(As, Ls, Hs, hits, flush=True)
