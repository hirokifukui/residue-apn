# Construct lifts with prescribed Taylor data at chosen class centres:  F_new = F + sum_s 2^t b_s (X - x)^s.
# Since (X-x)^s has Taylor coefficients delta_{s,i} at x, this changes F^[s](x) by 2^t b_s and keeps the residue p.
import random
from math import comb
from grlib import Ring, write_terms, read_terms
def expand_shift(R, x, s):
    """(X - x)^s as dict exponent -> coefficient tuple in R."""
    out = {}
    mx = R.smul(R.M - 1, x)
    for i in range(s + 1):
        c = R.smul(comb(s, i) % R.M, R.pw(mx, s - i))
        out[i] = c
    return out
def perturb(terms, R, x, bdict, t=1):
    """bdict: s -> coefficient tuple b_s (in R); adds 2^t * b_s (X-x)^s."""
    acc = {}
    for e, cd in terms:
        acc[e] = R.add(acc.get(e, R.zero), tuple(v % R.M for v in cd))
    for s, b in bdict.items():
        for i, c in expand_shift(R, x, s).items():
            acc[i] = R.add(acc.get(i, R.zero), R.smul(1 << t, R.mul(b, c)))
    return [(e, list(c)) for e, c in sorted(acc.items()) if any(c)]
def rand_el(R, rng, bits=None):
    b = R.K if bits is None else bits
    return tuple(rng.randrange(0, 1 << b) for _ in range(R.m))
