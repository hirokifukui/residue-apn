# Core library for R06: Galois-ring arithmetic, Taylor data of a lift at a class centre, the function T of a row,
# and the general digit recursion (Lemma GR of RESULT_R06.md) as an exact predictor.
import sys, json, random
from collections import Counter
from math import comb
sys.path.insert(0, '.')
from grlib import Field, Ring, res, read_terms, residue_coeffs, POLYS
from pinv import pinv

_PC = {}; _TC = {}
class Ctx:
    """Row context: lift F (terms), ring R_k, alpha = 2^j u."""
    def __init__(s, terms, m, k, alpha):
        s.m = m; s.k = k; s.terms = terms
        s.Fd = Field(m); s.q = s.Fd.q
        s.R = Ring(m, k)
        s.alpha = alpha
        s.j = s.R.val(alpha); s.n = k - s.j; s.d = s.n - 2
        s.Rn = Ring(m, s.n)
        u = tuple(v >> s.j for v in alpha)
        s.ubar = res(u)
        s.uinv = s.Rn.inv(tuple(v % (1 << s.n) for v in u))
        c = residue_coeffs(terms, m); key = tuple(sorted(c.items()))
        if key not in _PC: _PC[key] = pinv(c, m)
        s.P = _PC[key]; s.pc = c
        s.rho = s.P['rho']; s.mu = s.P['mu']; s.c3 = s.P['c3']; s.pi = s.P['pi']
        s.c5 = c.get(5, 0)
        if (m, k) not in _TC: _TC[(m, k)] = [s.R.pw(s.R.lift(y), s.q ** (k - 1)) for y in range(s.q)]
        s.teich = _TC[(m, k)]
        s.tau = s.teich[s.rho]
        s._tay = {}; s._tt = {}
    # Taylor coefficients f_s = F^[s](x), s < k, at a centre x
    def taylor(s, x, smax=None):
        if smax is None: smax = s.k
        if (x, smax) in s._tay: return s._tay[(x, smax)]
        R = s.R; fs = []
        for t in range(smax):
            acc = R.zero
            for e, cd in s.terms:
                if e < t: continue
                b = comb(e, t) % R.M
                if b == 0: continue
                coef = tuple((b * v) % R.M for v in cd)
                acc = R.add(acc, R.mul(coef, R.pw(x, e - t)))
            fs.append(acc)
        s._tay[(x, smax)] = fs
        return fs
    def ttaylor(s, x):
        """t_r = T^[r](x) mod 2^n for r < n, from t_r = sum_{s>r} binom(s,r) alpha^(s-r-1) f_s (exact identity)."""
        R = s.R; deg = max(e for e, _ in s.terms)
        # alpha^(t-r-1) f_t vanishes mod 2^k once j(t-r-1) >= k, so t <= n-1 + ceil(k/j) suffices
        deg = min(deg, s.n - 1 + -(-s.k // s.j))
        fs = s.taylor(x, deg + 1); out = []
        apow = [R.one]
        for i in range(deg + 1): apow.append(R.mul(apow[-1], s.alpha))
        for r in range(s.n):
            acc = R.zero
            for t in range(r + 1, deg + 1):
                b = comb(t, r) % R.M
                if b: acc = R.add(acc, R.smul(b, R.mul(apow[t - r - 1], fs[t])))
            out.append(tuple(v % (1 << s.n) for v in acc))
        return out
    def Tc(s, x, h):
        """T(x+h) in R_n for h in 2R, via the Taylor coefficients of T at x (exact: h^r in 2^r R)."""
        tt = s._tt.get(x)
        if tt is None: tt = s._tt[x] = s.ttaylor(x)
        Rn = s.Rn; hh = tuple(v % (1 << s.n) for v in h)
        acc = tt[-1]
        for r in range(s.n - 2, -1, -1): acc = Rn.add(Rn.mul(acc, hh), tt[r])
        return acc
    def Tc_F(s, x, h):
        """T(x+h) in R_n for h in 2R, via F(x+h)=sum_{t<k} f_t h^t (exact for h in 2R)."""
        R = s.R; fs = s.taylor(x)
        def P(hh):
            acc = fs[-1]
            for t in range(s.k - 2, -1, -1): acc = R.add(R.mul(acc, hh), fs[t])
            return acc
        D = R.sub(P(R.add(h, s.alpha)), P(h))
        assert all(v % (1 << s.j) == 0 for v in D)
        D = tuple((v >> s.j) % (1 << s.n) for v in D)
        return s.Rn.mul(D, s.uinv)
    def center(s, a):
        return s.teich[a]

def nz(c): return Counter({v: x for v, x in c.items() if v and x})

def sub_n(Rn, a, b, sh):
    """(a-b)/2^sh as tuple of ints mod 2^(n-sh); asserts divisibility."""
    D = Rn.sub(a, b)
    assert all(v % (1 << sh) == 0 for v in D), ('not divisible', D, sh)
    return tuple(v >> sh for v in D)

# ---------------- Lemma GR engine ----------------
# A node is (c, p, E, w): the polynomial  Phi(z) = (T(c + p + 2^E z) - B)/2^v  in the frame (B, v) of its configuration,
# counted with weight w.  A configuration is (B, v, [nodes]); its value at a target g in R/2^D (D = n - v) is
#   N(g) = sum_nodes w * #{z mod 2^D : Phi(z) = g mod 2^D}.
class GR:
    def __init__(s, ctx):
        s.C = ctx; s.calls = 0
    def Tpt(s, c, h):
        s.calls += 1
        return s.C.Tc(c, h)
    def config(s, B, v, nodes):
        """Return Counter of N(g) over all g in R/2^D (zeros included)."""
        C = s.C; q = C.q; R = C.R; Rn = C.Rn; D = C.n - v
        if D <= 0:
            return Counter({sum(w for _, _, _, w in nodes): 1})
        H = [0] * q
        groups = {}   # key (element of R/4 as tuple) -> (Bchild, [child nodes])
        for (c, p, E, w) in nodes:
            for y in range(q):
                hp = R.add(p, R.smul(1 << E, C.teich[y]))
                Ty = s.Tpt(c, hp)
                val = sub_n(Rn, Ty, B, v)          # Phi([y]) as tuple mod 2^(n-v)
                r = res(val)
                if D == 1:
                    H[r] += w; continue
                Ty2 = s.Tpt(c, R.add(hp, R.smul(1 << (E + 1), R.one)))
                crit = all(((a - b) % (1 << (v + 2))) == 0 for a, b in zip(Ty2, Ty))
                if not crit:
                    H[r] += w
                else:
                    key = tuple(x % 4 for x in val)
                    if key not in groups: groups[key] = (Ty, [])
                    groups[key][1].append((c, hp, E + 1, w * q))
        out = Counter()
        if D == 1:
            for r in range(q): out[H[r]] += 1
            return out
        used = Counter()
        for key, (Bc, ch) in groups.items():
            r = res(key)
            sub = s.config(Bc, v + 2, ch)
            for x, cnt in sub.items(): out[H[r] + x] += cnt
            used[r] += 1
        for r in range(q):
            rest = q ** (D - 1) - used[r] * q ** (D - 2)
            if rest: out[H[r]] += rest
        return out

def row_configs(ctx):
    """Split the row into pair configurations (Theorem A): list of (label, B, [nodes]) with v=2."""
    C = ctx; q = C.q; R = C.R; Rn = C.Rn
    out = []; done = set()
    for a in range(q):
        if a in done: continue
        b = a ^ C.rho; done |= {a, b}
        xa = C.center(a); xb = R.add(xa, C.tau)     # centre of class b := x_a + tau
        Ta = C.Tc(xa, R.zero); Tb = C.Tc(xb, R.zero)
        Bab = sub_n(Rn, Tb, Ta, 1)
        if res(Bab) == 0:
            out.append(((a, b), Ta, [(xa, R.zero, 1, 1), (xb, R.zero, 1, 1)]))
        else:
            out.append(((a,), Ta, [(xa, R.zero, 1, 1)]))
            out.append(((b,), Tb, [(xb, R.zero, 1, 1)]))
    return out

def gr_row(ctx):
    g = GR(ctx); tot = Counter(); per = {}
    for lab, B, nodes in row_configs(ctx):
        M = g.config(B, 2, nodes)
        per[lab] = M
        for N, cnt in M.items():
            if N: tot[N * ctx.q ** (ctx.j + 1)] += cnt
    return tot, per, g.calls

def make_alpha(R, j, ub, seed=1):
    rng = random.Random(seed)
    hi = tuple(rng.randrange(0, 1 << (R.K - j)) for _ in range(R.m))
    return R.smul(1 << j, R.add(R.lift(ub), R.smul(2, hi)))
