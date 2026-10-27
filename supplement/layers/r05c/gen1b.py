# Coordinate-scan generator for sub-case 1: conditions are predicates on successive DD levels (Theorem I data).
import json, sys, random
from gen1 import setup, merged_fix, ddlog
from gr import *
from closed import Fallback, nz
import closed; closed.FAST = True
from mklift import perturb, rand_el
from grlib import write_terms
m = 5
def lvl(log, L):
    e = [x for x in log if x[0] == L and x[1] in ('res', 'nonres', 'D=2', 'D=1')]
    return e[0] if e else None
def sat(log, spec):
    """spec: list of (level, predicate); score = number of leading conditions satisfied."""
    for i, (L, w) in enumerate(spec):
        e = lvl(log, L)
        if e is None or not w(e): return i
    return len(spec)
def scan(base, k, j, ub, seed, spec, params, rounds=6):
    T0, R, alpha, a = setup(base, k, j, ub, seed); rng = random.Random(seed)
    xa = Ctx(T0, m, k, alpha).center(a)
    T, C = merged_fix(perturb(T0, R, xa, {s: rand_el(R, rng) for s in range(2, 9)}, 1), R, alpha, a, k)
    def score(C):
        try:
            pre = 0
            if PRE.get(id(spec)):
                if not nuprime_zero(C, a): return 0, None, None
                pre = 1
            log, M = ddlog(C, a); return pre + sat(log, spec), log, M
        except Fallback:
            return -1, None, None
    sc, log, M = score(C)
    for rnd in range(rounds):
        if sc == len(spec) + (1 if PRE.get(id(spec)) else 0): break
        improved = False
        for (s, t) in params:
            for v in rng.sample(range(1, 32), 31):
                T1, C1 = merged_fix(perturb(T, R, xa, {s: R.lift(v)}, t), R, alpha, a, k)
                s1, l1, M1 = score(C1)
                if s1 > sc:
                    T, C, sc, log, M = T1, C1, s1, l1, M1; improved = True; break
            if sc == len(spec) + (1 if PRE.get(id(spec)) else 0): break
        if not improved:
            T, C = merged_fix(perturb(T, R, xa, {s: rand_el(R, rng) for s in range(4, 9)}, 2), R, alpha, a, k)
            sc, log, M = score(C)
    if sc != len(spec) + (1 if PRE.get(id(spec)) else 0): return None
    return T, C, a, log, M, alpha
res_i1 = lambda e: e[1] == 'res' and e[5] == 1
res_i0 = lambda e: e[1] == 'res' and e[5] == 0
res_any = lambda e: e[1] == 'res'
nonres = lambda e: e[1] == 'nonres'
nonres_ia = lambda e: e[1] == 'nonres' and e[5] == 1
nonres_ib = lambda e: e[1] == 'nonres' and e[6] == 1
d2 = lambda s: (lambda e: e[1] == 'D=2' and e[2] == s)
R0 = [(0, res_any)]; R1 = R0 + [(0, res_i1)]
Rq = R0 + [(0, lambda e: e[1] == 'res' and e[3] == 32)]          # nu' = 0 and full coincidence (then i = 1)
R1s1 = R0 + [(0, lambda e: e[1] == 'res' and e[3] == 1 and e[5] == 1)]   # nu' != 0, C = {t*}
SPECS = {'res_i0': R0 + [(0, res_i0)], 'res_i1': R1, 'res_i1_d2q': Rq + [(1, d2(32))], 'res_i1_d2s0': R1 + [(1, d2(0))],
         'res_i1_d2s1': Rq + [(1, d2(1))], 'res_i1_d2s2': R1s1 + [(1, d2(2))], 'res_i1_nonres': R1 + [(1, nonres)],
         'res_i1_res_i1': R1 + [(1, res_any), (1, res_i1)], 'res_i1_res_i0': R1 + [(1, res_any), (1, res_i0)],
         'nonres_ia': [(0, nonres), (0, nonres_ia)], 'nonres_ib': [(0, nonres), (0, nonres_ib)],
         'res_i1_res': R1 + [(1, res_any)], 'nonres': [(0, nonres)]}
def nuprime_zero(C, a):
    from closed import Node, deg_data, fit
    R = C.R; F = C.Fd; xa = C.center(a); xb = R.add(xa, C.tau)
    out = []
    for x in (xa, xb):
        nd = Node(C, x, R.zero, 1, 2); c, sig, lam = deg_data(nd)
        sg = [__import__('closed').witt2(C, nd.val(y))[1] for y in (1, 2, 4)]
        out.append(__import__('closed').solve_add(F, lambda y: __import__('closed').witt2(C, nd.val(y))[1]).get(2, 0))
    return out[0] == out[1]
PRE = {id(SPECS['res_i1_d2q']): True, id(SPECS['res_i1_d2s1']): True}
PARAMS = [(7, 1), (2, 1), (3, 1), (2, 2), (3, 2), (2, 3), (4, 1), (4, 2), (2, 4), (4, 3), (5, 2), (6, 1), (6, 2), (8, 1), (8, 2), (2, 5), (4, 4), (3, 3)]
if __name__ == '__main__':
    jobs = json.loads(sys.argv[1]); out = sys.argv[2]
    for base, k, j, ub, seed, sn in jobs:
        r = scan(base, k, j, ub, seed, SPECS[sn], PARAMS)
        if r is None: print('FAILED', base, k, j, ub, seed, sn, flush=True); continue
        T, C, a, log, M, alpha = r
        fn = f'lifts_r06/s1_{base}_k{k}j{j}u{ub}_s{seed}_{sn}.txt'; write_terms(fn, T)
        rec = dict(file=fn, k=k, j=j, ubar=ub, alpha=C.R.pack(alpha), a=a, spec=sn, log=log, pred=dict(nz(M)))
        open(out, 'a').write(json.dumps(rec) + "\n"); print('OK', base, k, j, sn, log, flush=True)
