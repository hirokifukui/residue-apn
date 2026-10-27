# Symbolic check of the family theorem for all c (m<=13) : invariants vs. predictions.
import sys, json, random
sys.path.insert(0, '/home/claude/w/research/sparse_r06')
from family import *
out = {}
for m in map(int, sys.argv[1:]):
    F = GF(m); q = F.q
    cs = range(q) if m <= 13 else None
    stat = dict(total=0, injective=0, inj_notF2=0, H=0, mu0=0, Z_empty=0, pred_match=0, mismatch=0, rho_ne1=0)
    nt = set(); deg = set(); goods = []
    for c in cs:
        B = Bco(F, c); stat['total'] += 1
        inj = lin_invertible(F, B)
        if not inj:
            pred = False
            iv = None
        else:
            stat['injective'] += 1
            cl = poly_of(F, c)
            iv = invariants(F, *cl)
        pred = inj and c not in (0, 1)
        got = bool(iv and iv['H'] and iv['mu'] == 0 and iv['z'] == 0)
        if inj and c not in (0, 1):
            stat['inj_notF2'] += 1
            rho = solve_lin(F, B, 1)
            ok = (iv['H'] and iv['rho'] == rho and iv['eps'] == 1 and iv['mu'] == 0 and iv['z'] == 0 and rho != 1)
            stat['H'] += iv['H']; stat['mu0'] += (iv['mu'] == 0); stat['Z_empty'] += (iv['z'] == 0); stat['rho_ne1'] += (rho != 1)
            if ok: goods.append(c)
            nt.add(nterms(cl))
            cdict, ldict = cl
            deg.add(max([(1 << u) + (1 << v) for (u, v) in cdict] + [1 << w for w in ldict]))
        if got == pred: stat['pred_match'] += 1
        else: stat['mismatch'] += 1
    stat['nterms'] = sorted(nt); stat['degrees'] = sorted(deg); stat['admissible_c_sample'] = goods[:8]; stat['n_admissible'] = len(goods)
    out[m] = stat
    print(m, json.dumps(stat), flush=True)
json.dump(out, open('/home/claude/w/research/sparse_r06/out/check_family_%s.json' % '_'.join(sys.argv[1:]), 'w'), indent=1)
