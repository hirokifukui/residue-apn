import sys, itertools, random
sys.path.insert(0, '.')
from sym import *
m = int(sys.argv[1]); N = int(sys.argv[2]); F = GF(m); random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
# shapes: A support (with a0=1 normalized), L support (with l0 or first =1)
stats = {}
for As in [s for r in (2, 3) for s in itertools.combinations(range(m), r) if 0 in s]:
    for Ls in [s for r in (1, 2) for s in itertools.combinations(range(m), r) if 0 in s]:
        H = hit = tried = 0
        for _ in range(N):
            A = {k: (1 if k == 0 else random.randrange(1, F.q)) for k in As}
            L = {k: (1 if k == 0 else random.randrange(1, F.q)) for k in Ls}
            if not (lin_invertible(F, A) and lin_invertible(F, L)): continue
            tried += 1
            iv = invariants(F, *expand_LA3(F, A, L))
            if iv['H']:
                H += 1
                if iv['mu'] == 0 and iv['z'] == 0: hit += 1
        if H: print(As, Ls, tried, H, hit, flush=True)
