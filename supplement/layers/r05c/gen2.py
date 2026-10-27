# Sub-case 2 lifts: merged DEEP+DEEP pair (mu=0=c3, pi(a)=0, A_F(a)=0), prescribed half-pair data.
import json, sys, random
from gr import *
from closed import Node, node_kind, offset, shape, deg_data, Fallback, theorem2_pair, nz
import closed; closed.FAST = True
from mklift import perturb, rand_el
from grlib import write_terms
m = 5; idx = json.load(open('lifts/index.json'))
def merged_fix(T, R, alpha, a, k):
    C = Ctx(T, m, k, alpha); F = C.Fd; xa = C.center(a); xb = R.add(xa, C.tau)
    Bv = res(sub_n(C.Rn, C.Tc(xb, R.zero), C.Tc(xa, R.zero), 1))
    if Bv:
        T = perturb(T, R, xa, {5: R.lift(F.mul(Bv, F.inv(F.pow(C.rho, 4))))}, 1); C = Ctx(T, m, k, alpha)
        assert res(sub_n(C.Rn, C.Tc(xb, R.zero), C.Tc(xa, R.zero), 1)) == 0
    return T, C
def desc(C, a):
    R = C.R; F = C.Fd; xa = C.center(a); xb = R.add(xa, C.tau)
    A = Node(C, xa, R.zero, 1, 2); B = Node(C, xb, R.zero, 1, 2)
    e = offset(A, B); d = dict(eb=res(e))
    for nm, X in (('a', A), ('b', B)):
        h = X.half(); kd, w, c = node_kind(h); d['k' + nm] = kd; d['w' + nm] = w; d['c' + nm] = c
        if kd == 'DEEP' and h.D >= 2:
            co = shape(h.half()); d['l1' + nm] = co.get(1, 0)
    if d['ka'] == 'ND' and d['kb'] == 'ND' and d['ca'] and d['cb']:
        d['samehyp'] = F.mul(d['ca'], F.inv(F.mul(d['wa'], d['wa']))) == F.mul(d['cb'], F.inv(F.mul(d['wb'], d['wb'])))
        if d['samehyp'] and d['eb'] == 0:
            eps = res(tuple(v // 2 for v in e))
            d['chi'] = F.tr(F.mul(F.mul(d['cb'], eps), F.inv(F.mul(d['wb'], d['wb']))))
    return d
E0 = lambda d: d['eb'] == 0
CONDS = {
 'split_gen':   [lambda d: d['eb'] != 0],
 'split_deg':   [lambda d: d['ka'] == 'DEG', lambda d: d['eb'] != 0],
 'split_deep2': [lambda d: d['ca'] == 0, lambda d: d['ka'] == 'DEEP', lambda d: d['eb'] != 0],
 'm_gen':       [lambda d: d['ka'] == 'ND' and d['kb'] == 'ND' and d['ca'] and d['cb'], E0, lambda d: not d['samehyp']],
 'm_same_chi0': [lambda d: d['ka'] == 'ND' and d['kb'] == 'ND' and d['ca'] != 0 and d['cb'] != 0,
                 lambda d: d['samehyp'], E0, lambda d: d['chi'] == 0],
 'm_same_chi1': [lambda d: d['ka'] == 'ND' and d['kb'] == 'ND' and d['ca'] != 0 and d['cb'] != 0,
                 lambda d: d['samehyp'], E0, lambda d: d['chi'] == 1],
 'm_c0':        [lambda d: d['ka'] == 'ND' and d['kb'] == 'ND', lambda d: d['ca'] == 0, E0],
 'm_nd_deg':    [lambda d: d['kb'] == 'ND', lambda d: d['ka'] == 'DEG', E0],
 'm_deg_deg':   [lambda d: d['ca'] != 0, lambda d: d['ka'] == 'DEG', lambda d: d['cb'] != 0, lambda d: d['kb'] == 'DEG', E0],
 'm_deep2_nd':  [lambda d: d['kb'] == 'ND', lambda d: d['ca'] == 0, lambda d: d['ka'] == 'DEEP', E0],
 'm_deep2_deg': [lambda d: d['ca'] == 0, lambda d: d['ka'] == 'DEEP', lambda d: d['kb'] == 'DEG', lambda d: d.get('l1a', 1) != 0, E0],
 'm_deep2_deep2': [lambda d: d['ca'] == 0, lambda d: d['ka'] == 'DEEP', lambda d: d['cb'] == 0, lambda d: d['kb'] == 'DEEP', E0],
}
PARAMS = [(ci, s, t) for ci in (0, 1) for s in (2, 3, 1, 4, 5, 6, 7) for t in (1, 2, 3)]
def scan(base, a, k, j, ub, seed, conds, rounds=8):
    T0 = read_terms(idx[base]['file'], m); R = Ring(m, k); rng = random.Random(seed)
    alpha = make_alpha(R, j, ub, seed); C = Ctx(T0, m, k, alpha); xa = C.center(a); xb = R.add(xa, C.tau)
    cen = [xa, xb]
    T, C = merged_fix(perturb(T0, R, xa, {s: rand_el(R, rng) for s in range(4, 9)}, 1), R, alpha, a, k)
    def score(C):
        try: d = desc(C, a)
        except Exception: return -1, None
        for i, c in enumerate(conds):
            try:
                if not c(d): return i, d
            except Exception: return i, d
        return len(conds), d
    sc, d = score(C)
    for rnd in range(rounds):
        if sc == len(conds): break
        improved = False
        ps = PARAMS[:]; rng.shuffle(ps)
        for (ci, s, t) in ps:
            for v in rng.sample(range(1, 32), 31):
                T1, C1 = merged_fix(perturb(T, R, cen[ci], {s: R.lift(v)}, t), R, alpha, a, k)
                s1, d1 = score(C1)
                if s1 > sc: T, C, sc, d = T1, C1, s1, d1; improved = True; break
            if sc == len(conds): break
        if not improved:
            T, C = merged_fix(perturb(T, R, xa, {s: rand_el(R, rng) for s in range(4, 9)}, 2), R, alpha, a, k); sc, d = score(C)
    if sc != len(conds): return None
    return T, C, alpha, d
if __name__ == '__main__':
    jobs = json.loads(sys.argv[1]); out = sys.argv[2]
    for base, a, k, j, ub, seed, cn in jobs:
        r = scan(base, a, k, j, ub, seed, CONDS[cn])
        if r is None: print('FAILED', base, k, j, cn, flush=True); continue
        T, C, alpha, d = r
        fn = f'lifts_r06/s2_{base}_a{a}_k{k}j{j}u{ub}_{cn}_s{seed}.txt'; write_terms(fn, T)
        rec = dict(file=fn, k=k, j=j, ubar=ub, alpha=C.R.pack(alpha), a=a, spec=cn, desc=d)
        open(out, 'a').write(json.dumps(rec) + "\n"); print('OK', fn, d, flush=True)
