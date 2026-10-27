# Generic coordinate tuner: find a lift (perturbation of a base lift by 2^t b (X-x)^s at chosen centres) such that a
# list of conditions holds.  Conditions are evaluated on the Ctx of the candidate lift.
import random
from gr import Ctx, Ring, res
from mklift import perturb
def ok_upto(C, conds, i):
    for c in conds[:i + 1]:
        try:
            if not c(C): return False
        except Exception:
            return False
    return True
def tune(T0, m, k, alpha, centers, conds, rng, params=None, verbose=False):
    R = Ring(m, k); T = T0
    if params is None:
        params = [(ci, s, t) for ci in range(len(centers)) for s in range(1, 11) for t in (1, 2, 3)]
    C = Ctx(T, m, k, alpha)
    for i, cond in enumerate(conds):
        if ok_upto(C, conds, i): continue
        found = False
        ps = params[:]; rng.shuffle(ps)
        for (ci, s, t) in ps:
            vals = list(range(1, 1 << m)); rng.shuffle(vals)
            for v in vals:
                T1 = perturb(T, R, centers[ci], {s: R.lift(v)}, t)
                C1 = Ctx(T1, m, k, alpha)
                if ok_upto(C1, conds, i):
                    T, C = T1, C1; found = True; break
            if found: break
        if verbose: print('cond', i, 'found' if found else 'FAILED', flush=True)
        if not found: return None, None
    return T, C
