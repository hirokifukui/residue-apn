# test_hull_layer.py (Claude, R06, 2026-10-26): exhaustive check of the layerwise two-round bound
# (Proposition hullunit, R06 form) on GR(4,2), n = 2 words, an MDS layer M = [[1,1],[1,t]] (B = 3), for random
# residue-preserving permutations G of GR(4,2) (these preserve the 2-adic valuation of differences, k = 2).
# For every input difference a != 0 of layer s (s = min word valuation) and every output difference c:
#     Pr[a -> c after two rounds] <= (D_s / q^k)^(B-1)            (no factor 2^n),
# with D_s the largest DDT entry over inputs of exact valuation s. Exact integer arithmetic (numpy int64).
import random, sys
import numpy as np
R = [(a, b) for a in range(4) for b in range(4)]          # Z/4[t]/(t^2+t+1)
idx = {r: i for i, r in enumerate(R)}
def add(x, y): return ((x[0] + y[0]) % 4, (x[1] + y[1]) % 4)
def sub(x, y): return ((x[0] - y[0]) % 4, (x[1] - y[1]) % 4)
def mul(x, y):
    a0, a1 = x; b0, b1 = y
    c0 = a0 * b0; c1 = a0 * b1 + a1 * b0; c2 = a1 * b1
    return ((c0 - c2) % 4, (c1 - c2) % 4)
def res(x): return (x[0] % 2, x[1] % 2)
def val(x):
    if x == (0, 0): return 2
    return 0 if res(x) != (0, 0) else 1
t = (0, 1); one = (1, 0)
Mm = [[one, one], [one, t]]
V = [(x, y) for x in R for y in R]
vidx = {v: i for i, v in enumerate(V)}
def Mv(v): return tuple(add(mul(Mm[i][0], v[0]), mul(Mm[i][1], v[1])) for i in range(2))
perm = np.array([vidx[Mv(v)] for v in V])
assert len(set(perm.tolist())) == 256
# branch number of M over the residue field is 3 (MDS 2x2): check on F4
B = 3
def run(seed):
    random.seed(seed)
    resid = [(0, 0), (0, 1), (1, 0), (1, 1)]
    pi = resid[:]; random.shuffle(pi)
    G = {}
    for a, b in zip(resid, pi):
        cls = [x for x in R if res(x) == a]; tgt = [x for x in R if res(x) == b]; random.shuffle(tgt)
        for x, y in zip(cls, tgt): G[x] = y
    D = np.zeros((16, 16), dtype=np.int64)
    for al in R:
        for x in R:
            D[idx[al], idx[sub(G[add(x, al)], G[x])]] += 1
    # valuation preservation of G (k = 2)
    for al in R:
        for be in R:
            if D[idx[al], idx[be]] and al != (0, 0): assert val(al) == val(be)
    Ds = {s: int(max(D[idx[al], j] for al in R if val(al) == s for j in range(16))) for s in (0, 1)}
    PS = np.kron(D, D)                                   # word-pair DDT, scaled by 256
    P = np.zeros((256, 256), dtype=np.int64); P[np.arange(256), perm] = 1
    T = PS @ P @ PS                                      # Pr = T / 256^2
    bad = 0; tight = {0: 0, 1: 0}
    for ia, a in enumerate(V):
        if ia == vidx[((0, 0), (0, 0))]: continue
        s = min(val(a[0]), val(a[1]))
        lhs = T[ia].max()                                # Pr * 256^2
        rhs = Ds[s] ** (B - 1) * 256 ** 2 // 16 ** (B - 1)   # (D_s/16)^(B-1) * 256^2, exact (16^2 | 256^2)
        if lhs > rhs: bad += 1
        if lhs == rhs: tight[s] += 1
    return Ds, bad, tight
total_bad = 0
for seed in range(32):
    Ds, bad, tight = run(seed)
    print(seed, "D0=%d D1=%d" % (Ds[0], Ds[1]), "violations=%d" % bad, "tight(s0,s1)=%d,%d" % (tight[0], tight[1]),
          "ok" if bad == 0 else "FAIL")
    total_bad += bad
if total_bad:
    print("HULL_LAYER FAIL"); sys.exit(1)
print("HULL_LAYER OK 32 seeds, all 255 inputs x 256 outputs each, bound (D_s/q^k)^(B-1) without 2^n")
