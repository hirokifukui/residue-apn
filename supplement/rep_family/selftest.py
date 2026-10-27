# brute-force cross-check of sym.py against direct evaluation / interpolation-free checks for small m
import sys, random
sys.path.insert(0, '.')
from sym import *

def brute(F, f):
    # f: list of values; compute reduced poly coefficients at needed exponents via c_e = sum_a f(a) a^(q-1-e)
    q = F.q; m = F.m
    def coef(e):
        if e == 0: return f[0]
        s = 0
        for a in range(1, q):
            if f[a]: s ^= F.mul(f[a], F.pow(a, q - 1 - e))
        return s
    c = {}; l = {}
    for u in range(m):
        for v in range(u + 1, m):
            x = coef((1 << u) + (1 << v))
            if x: c[(u, v)] = x
        x = coef(1 << u)
        if x: l[u] = x
    return c, l

random.seed(1)
for m in (5, 7):
    F = GF(m); n = 0
    while n < 30:
        A = {k: random.randrange(F.q) for k in random.sample(range(m), 2)}
        L = {k: random.randrange(F.q) for k in random.sample(range(m), 2)}
        if not (lin_invertible(F, A) and lin_invertible(F, L)): continue
        def lin(co, x):
            s = 0
            for k, a in co.items(): s ^= F.mul(a, F.frob(x, k))
            return s
        f = [lin(L, F.pow(lin(A, x), 3)) for x in range(F.q)]
        c, l = expand_LA3(F, A, L)
        cb, lb = brute(F, f)
        assert (c, l) == (cb, lb), (m, A, L)
        assert all(peval(F, c, l, x) == f[x] for x in range(F.q))
        iv = invariants(F, c, l)
        if iv['H']:
            # brute Z and mu check
            rho = iv['rho']
            def dp(x):
                s = l.get(0, 0)
                for (u, v), cc in c.items():
                    if u == 0: s ^= F.mul(cc, F.frob(x, v))
                return s
            Z = [a for a in range(F.q) if f[a ^ rho] ^ f[a] ^ F.mul(rho, dp(a)) == 0]
            assert len(Z) == iv['z'], (len(Z), iv)
            assert len({dp(a) for a in range(F.q)}) == F.q // 2 and 0 not in {dp(a) for a in range(F.q)}
        n += 1
print("selftest ok")
