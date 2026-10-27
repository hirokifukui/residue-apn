# symbolic (q-independent) verification of the theorem for p_d = (Tr(x) + d x^(2^(m-2)))^3, using sym.py
# predictions: A_d invertible <=> Tr(1/d)=0 ; then rho=d^-4, eps=(1+d)^2, mu=0, Z empty always; (H) <=> Tr(d)=0
import sys, json, random, time
sys.path.insert(0, '.')
from sym import *
def check(F, d):
    m = F.m
    A = {i: 1 for i in range(m)}; A[m-2] ^= d
    td, tid = F.tr(d), F.tr(F.inv(d))
    inv_ok = lin_invertible(F, A)
    rec = dict(d=d, Tr_d=td, Tr_inv_d=tid, invertible=inv_ok)
    ok = (inv_ok == (tid == 0))
    if inv_ok:
        c, l = expand_LA3(F, A, {0: 1})
        iv = invariants(F, c, l)   # note: invariants() returns H=False if eps in Im K
        # recompute K-kernel/mu/z regardless of eps for the record
        rec.update(H=iv['H'], why=iv.get('why'))
        if iv['H']:
            rec.update(rho=iv['rho'], mu=iv['mu'], z=iv['z'], eps=iv['eps'])
            ok = ok and td == 0 and iv['rho'] == F.pow(F.inv(d), 4) and iv['mu'] == 0 and iv['z'] == 0 and iv['eps'] == F.sq(1 ^ d)
        else:
            ok = ok and td == 1 and iv.get('why') == 'eps in ImK'
    rec['agrees'] = ok
    return rec
res = {}
mode = sys.argv[1]
ms = [int(x) for x in sys.argv[2].split(',')]
for m in ms:
    F = GF(m); t0 = time.time(); recs = []
    if mode == 'all':
        ds = range(1, F.q)
    else:
        random.seed(1000 + m); N = int(sys.argv[3]); a = b = 0; ds = []
        while a < N or b < N:
            d = random.randrange(2, F.q)
            pr = F.tr(d) == 0 and F.tr(F.inv(d)) == 0
            if pr and a < N: a += 1; ds.append(d)
            elif not pr and b < N: b += 1; ds.append(d)
    for d in ds: recs.append(check(F, d))
    s = dict(m=m, poly=F.P, mode=mode, tested=len(recs), agree=sum(r['agrees'] for r in recs),
             hits=sum(1 for r in recs if r.get('H') and r['mu'] == 0 and r['z'] == 0), seconds=round(time.time() - t0, 1))
    print(json.dumps(s), flush=True)
    res[m] = dict(summary=s, records=recs)
json.dump(res, open('out/symcheck_%s_%s.json' % (mode, sys.argv[2].replace(',', '_')), 'w'))
