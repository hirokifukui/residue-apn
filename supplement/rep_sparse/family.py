# Sparse family: B_c(x) = x^(2^(m-2)) + x^(2^(m-1)) + x + x^2 + c x^4,  p_c = reduced poly of B_c(x)^3.
import sys
sys.path.insert(0, '/home/claude/w/research/sparse_r06')
from sym import GF, expand_LA3, invariants, lin_invertible, rank
def Bco(F, c):
    m = F.m
    return {m-2: 1, m-1: 1, 0: 1, 1: 1, 2: c}
def apply(F, op, x):
    s = 0
    for k, a in op.items(): s ^= F.mul(a, F.frob(x, k))
    return s
def solve_lin(F, op, rhs):
    """unique x with op(x) = rhs (op invertible), by Gaussian elimination over F2"""
    m = F.m
    cols = [apply(F, op, 1 << i) for i in range(m)]
    # augmented rows: find combination of cols equal rhs
    basis = []  # (img, combo)
    for i, v in enumerate(cols):
        comb = 1 << i
        for bimg, bcomb in basis:
            if v ^ bimg < v: v ^= bimg; comb ^= bcomb
        if v: basis.append((v, comb)); basis.sort(key=lambda t: -t[0])
    v = rhs; comb = 0
    for bimg, bcomb in basis:
        if v ^ bimg < v: v ^= bimg; comb ^= bcomb
    assert v == 0
    return comb
def poly_of(F, c):
    return expand_LA3(F, Bco(F, c), {0: 1})
def nterms(cl):
    c, l = cl
    return len(c) + len(l)
