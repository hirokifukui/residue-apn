# write term files (inv.py format) for the first admissible d's, and record sym.py invariants
import sys, json
sys.path.insert(0, '.')
from sym import *
out = []
for m, nd in ((5, 3), (7, 3), (9, 2), (11, 2), (13, 1)):
    F = GF(m); k = 0
    for d in range(2, F.q):
        if F.tr(d) or F.tr(F.inv(d)): continue
        A = {i: 1 for i in range(m)}; A[m-2] ^= d
        c, l = expand_LA3(F, A, {0: 1})
        iv = invariants(F, c, l)
        fn = 'terms/fam_m%d_d%d.txt' % (m, d)
        write_terms(F, c, l, fn)
        out.append(dict(m=m, d=d, file=fn, sym=dict(H=iv['H'], rho=iv['rho'], mu=iv['mu'], z=iv['z'], eps=iv['eps']),
                        rho_pred=F.pow(F.inv(d), 4)))
        k += 1
        if k == nd: break
json.dump(out, open('out/terms_index.json', 'w'), indent=1)
for o in out: print(o['file'])
