# Symbolic (q-free) check of Theorem 1 for sampled c, m = 15..31: predictions vs sym.invariants
import sys, json, random
sys.path.insert(0, '/home/claude/w/research/sparse_r06')
from family import *
res = {}
for m in range(15, 33, 2):
    F = GF(m); random.seed(1000 + m); inj = good = agree = tested = 0; nt = set()
    while inj < 20:
        c = random.randrange(2, F.q); tested += 1
        B = Bco(F, c)
        if not lin_invertible(F, B): continue
        inj += 1
        cl = poly_of(F, c); iv = invariants(F, *cl); rho = solve_lin(F, B, 1)
        ok = iv['H'] and iv['rho'] == rho and rho != 1 and iv['eps'] == 1 and iv['mu'] == 0 and iv['z'] == 0
        agree += ok; nt.add(nterms(cl))
    res[m] = dict(poly=F.P, sampled_c=tested, injective=inj, agree=agree, nterms=sorted(nt))
    print(m, json.dumps(res[m]), flush=True)
json.dump(res, open('/home/claude/w/research/sparse_r06/out/check_family_sample_15_31.json', 'w'), indent=1)
