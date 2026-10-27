# Sub-case 3, lambda1 = 0 with lambda2*c5 != 0: resonant (theta^2 = lambda2 c5) fibre pairs, with/without
# coincidence and with zeros of mu (degenerate children), to exercise Theorem III(5) with T1/T2/Theorem P groups.
import json, sys, random
from gr import *
from gen3 import build
from closed import Node, shape, witt2, quarter_multiset, Fallback
from tune import tune
from pinv import peval
from grlib import write_terms
m = 5
def setup(base, a, k, j, ub, seed, resonant):
    # build with mode Z1, then overwrite lambda2 by solving for the target
    import gen3
    rng = random.Random(seed)
    T, C, alpha, info = build(base, a, k, j, ub, 'Z1', 'split', seed)
    return T, C, alpha, info
def conds_for(a, want_res, want_coinc, want_zero):
    def psi(C): return Node(C, C.center(a), C.R.zero, 1, 4)
    def theta(C): return peval(C.Fd, C.pc, a, 4) ^ (C.Fd.mul(C.ubar, C.c5) if C.j == 1 else 0)
    def co(C): return shape(psi(C))
    def l1zero(C): return co(C).get(1, 0) == 0
    def res_ok(C):
        F = C.Fd; l2 = co(C).get(2, 0); th = theta(C)
        return l2 != 0 and ((F.mul(th, th) == F.mul(l2, C.c5)) == want_res)
    def coinc(C):
        F = C.Fd; l2 = co(C).get(2, 0); eta = F.sqrt(F.mul(l2, F.inv(C.c5))); P = psi(C)
        cnt = sum(1 for y in range(32) if all(((u - v) % 4) == 0 for u, v in zip(P.val(y), P.val(y ^ eta)))) // 2
        return (cnt > 0) == want_coinc
    def zero(C):
        P = psi(C); F = C.Fd; l2 = co(C).get(2, 0); th = theta(C)
        mu0 = shape(P.child(0)).get(1, 0)
        has = any((F.mul(th, F.mul(y, y)) ^ F.mul(l2, y) ^ mu0) == 0 for y in range(32))
        return has == want_zero
    return [l1zero, res_ok, zero, coinc]
if __name__ == '__main__':
    jobs = json.loads(sys.argv[1]); out = sys.argv[2]
    for base, a, k, j, ub, seed, wres, wco, wz in jobs:
        rng = random.Random(seed)
        T0, C0, alpha, info = setup(base, a, k, j, ub, seed, wres)
        F = C0.Fd; th = peval(F, C0.pc, a, 4) ^ (F.mul(C0.ubar, C0.c5) if C0.j == 1 else 0)
        # set lambda2 to theta^2/c5 (resonant) by shifting f_3 mod 8: lambda2 += res(b), b at (3,2)
        P = Node(C0, C0.center(a), C0.R.zero, 1, 4); l2 = shape(P).get(2, 0)
        target = F.mul(F.mul(th, th), F.inv(C0.c5)) if wres else (l2 if F.mul(th, th) != F.mul(l2, C0.c5) else l2 ^ 1)
        from mklift import perturb
        R = C0.R; b = l2 ^ target
        T1 = perturb(T0, R, C0.center(a), {3: R.lift(b), 2: R.lift(F.mul(C0.ubar, b) if C0.j == 1 else 0)}, 2) if b else T0
        params = [(0, s, t) for s in (2, 3) for t in (3, 4)] + [(0, s, t) for s in (4, 5, 6, 7) for t in (2, 3)]
        cs = conds_for(a, wres, wco, wz)
        Tn, Cn = tune(T1, m, k, alpha, [C0.center(a)], cs[:3], rng, params)
        if Tn is not None and not cs[3](Cn):
            # combined move: f_3 += 8v, f_2 += 8*ubar*v keeps mu0 (j=1) and shifts nu2 -> moves the coincidence constant only
            got = None
            for v in range(1, 32):
                T2 = perturb(Tn, R, C0.center(a), {3: R.lift(v), 2: R.lift(F.mul(C0.ubar, v) if C0.j == 1 else 0)}, 3)
                C2 = Ctx(T2, m, k, alpha)
                if all(c(C2) for c in cs): got = (T2, C2); break
            Tn, Cn = got if got else (None, None)
        if Tn is None: print('FAILED', base, k, j, wres, wco, wz, flush=True); continue
        lg = []
        try: quarter_multiset(Node(Cn, Cn.center(a), R.zero, 1, 4), lg)
        except Fallback as ex: lg.append(('FB', str(ex)))
        fn = f'lifts_r06/s3b_{base}_a{a}_k{k}j{j}u{ub}_r{int(wres)}c{int(wco)}z{int(wz)}_s{seed}.txt'; write_terms(fn, Tn)
        rec = dict(file=fn, k=k, j=j, ubar=ub, alpha=R.pack(alpha), a=a, mode='Z1b', merge='split', spec=f'III5 res{int(wres)} coinc{int(wco)} zero{int(wz)}', log=[str(x) for x in lg])
        open(out, 'a').write(json.dumps(rec) + "\n"); print('OK', fn, lg, flush=True)
