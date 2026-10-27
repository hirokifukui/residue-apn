# Symbolic invariants of reduced quadratic p over GF(2^m), no dependence on q-sized loops.
# p is given by: c[(u,v)] (u<v) coefficient of X^(2^u+2^v), l[u] coefficient of X^(2^u), const.
import random

def find_irred(m):
    # smallest-weight irreducible: trinomial, else pentanomial; test via x^(2^m)=x mod f and gcd conditions
    def pmod(a, f):
        df = f.bit_length() - 1
        while a.bit_length() - 1 >= df:
            a ^= f << (a.bit_length() - 1 - df)
        return a
    def pmulmod(a, b, f):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a >> (f.bit_length() - 1) & 1: a ^= f
        return r
    def pgcd(a, b):
        while b: a, b = b, pmod(a, b)
        return a
    def irreducible(f):
        n = f.bit_length() - 1
        x = 2; y = x
        for i in range(1, n // 2 + 1):
            y = pmulmod(y, y, f)
            if pgcd(f, y ^ x) != 1: return False
        return True
    for k in range(1, m):
        f = (1 << m) | (1 << k) | 1
        if irreducible(f): return f
    for a in range(1, m):
        for b in range(a + 1, m):
            for c in range(b + 1, m):
                f = (1 << m) | (1 << c) | (1 << b) | (1 << a) | 1
                if irreducible(f): return f
    raise ValueError

POLYS = {5: 0b100101, 7: 0b10000011, 9: 0b1000010001, 11: (1 << 11) | 0b101, 13: (1 << 13) | 0b11011}

class GF:
    def __init__(s, m, poly=None):
        s.m = m; s.q = 1 << m
        s.P = poly or POLYS.get(m) or find_irred(m)
    def mul(s, a, b):
        r = 0; m = s.m; P = s.P; top = 1 << m
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a & top: a ^= P
        return r
    def sq(s, a): return s.mul(a, a)
    def frob(s, a, k):
        k %= s.m
        for _ in range(k): a = s.mul(a, a)
        return a
    def pow(s, a, e):
        r = 1
        while e:
            if e & 1: r = s.mul(r, a)
            a = s.mul(a, a); e >>= 1
        return r
    def inv(s, a): return s.pow(a, s.q - 2)
    def tr(s, a):
        t = 0; x = a
        for _ in range(s.m): t ^= x; x = s.mul(x, x)
        return t

# linear algebra over F2 on maps given as list of images of basis vectors 1<<i
def rank(cols, m):
    b = list(cols); r = 0
    for bit in range(m):
        piv = None
        for i in range(r, len(b)):
            if b[i] >> bit & 1: piv = i; break
        if piv is None: continue
        b[r], b[piv] = b[piv], b[r]
        for i in range(len(b)):
            if i != r and b[i] >> bit & 1: b[i] ^= b[r]
        r += 1
    return r

def kernel(F, cols, m):
    # kernel of linear map with images cols[i] of e_i: gaussian elimination tracking combos
    rows = [(cols[i], 1 << i) for i in range(m)]
    ker = []
    basis = []  # (img, combo) reduced
    for img, comb in rows:
        for bimg, bcomb in basis:
            if img ^ bimg < img: img ^= bimg; comb ^= bcomb
        if img == 0: ker.append(comb)
        else: basis.append((img, comb)); basis.sort(key=lambda t: -t[0])
    return ker

def in_span(cols, v):
    basis = []
    for c in cols:
        for b in basis:
            if c ^ b < c: c ^= b
        if c: basis.append(c); basis.sort(reverse=True)
    for b in basis:
        if v ^ b < v: v ^= b
    return v == 0

def expand_LA3(F, Acoef, Lcoef):
    """p = L(A(x)^3); Acoef, Lcoef dicts {k: coeff} for linearized polys sum coeff * x^(2^k).
    Returns (c, l) with reduced exponents."""
    m = F.m
    # A(x)^3 = A(x)^2 * A(x) = sum_{i,j} a_i^2 a_j x^(2^(i+1)+2^j)
    D = {}  # key (u,v) unordered as sorted tuple or ('L',u)
    def add(key, val):
        if val: D[key] = D.get(key, 0) ^ val
    for i, ai in Acoef.items():
        for j, aj in Acoef.items():
            val = F.mul(F.sq(ai), aj)
            u = (i + 1) % m; v = j % m
            if u == v: add(('L', (u + 1) % m), val)
            else: add(tuple(sorted((u, v))), val)
    c = {}; l = {}
    for k, lk in Lcoef.items():
        for key, val in D.items():
            w = F.mul(lk, F.frob(val, k))
            if not w: continue
            if key[0] == 'L':
                u = (key[1] + k) % m; l[u] = l.get(u, 0) ^ w
            else:
                u, v = (key[0] + k) % m, (key[1] + k) % m
                if u == v:
                    uu = (u + 1) % m; l[uu] = l.get(uu, 0) ^ w
                else:
                    kk = tuple(sorted((u, v))); c[kk] = c.get(kk, 0) ^ w
    c = {k: v for k, v in c.items() if v}; l = {k: v for k, v in l.items() if v}
    return c, l

def peval(F, c, l, x, const=0):
    s = const
    for (u, v), cc in c.items(): s ^= F.mul(cc, F.mul(F.frob(x, u), F.frob(x, v)))
    for u, cc in l.items(): s ^= F.mul(cc, F.frob(x, u))
    return s

def invariants(F, c, l):
    m = F.m
    eps = l.get(0, 0)
    Kc = {v: cc for (u, v), cc in c.items() if u == 0}
    def K(x):
        s = 0
        for v, cc in Kc.items(): s ^= F.mul(cc, F.frob(x, v))
        return s
    Kcols = [K(1 << i) for i in range(m)]
    ker = kernel(F, Kcols, m)
    out = dict(H=False)
    if len(ker) != 1: out['why'] = 'kerK dim %d' % len(ker); return out
    rho = ker[0]
    if in_span(Kcols, eps): out['why'] = 'eps in ImK'; return out
    mu = F.mul(c.get((0, 1), 0), rho)
    for (u, v), cc in c.items():
        if u == 1: mu ^= F.mul(cc, F.frob(rho, v))
    def B(a, b):
        s = 0
        for (u, v), cc in c.items():
            s ^= F.mul(cc, F.mul(F.frob(a, u), F.frob(b, v)) ^ F.mul(F.frob(b, u), F.frob(a, v)))
        return s
    Mcols = [B(1 << i, rho) ^ F.mul(rho, K(1 << i)) for i in range(m)]
    C = peval(F, c, l, rho) ^ F.mul(rho, eps)
    zempty = not in_span(Mcols, C)
    rM = rank(Mcols, m)
    z = 0 if zempty else (1 << (m - rM))
    out.update(H=True, rho=rho, eps=eps, mu=mu, z=z, rankM=rM, C=C)
    return out

def lin_invertible(F, coef):
    cols = []
    for i in range(F.m):
        x = 1 << i; s = 0
        for k, a in coef.items(): s ^= F.mul(a, F.frob(x, k))
        cols.append(s)
    return rank(cols, F.m) == F.m

def write_terms(F, c, l, fn, const=0):
    T = []
    if const: T.append((0, const))
    for u, cc in l.items(): T.append((1 << u, cc))
    for (u, v), cc in c.items(): T.append(((1 << u) + (1 << v), cc))
    T.sort()
    with open(fn, 'w') as f:
        f.write('%d\n' % len(T))
        for e, cc in T: f.write('%d %s\n' % (e, ' '.join(str(cc >> i & 1) for i in range(F.m))))
