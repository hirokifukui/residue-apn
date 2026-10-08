"""R3 independent checks (Claude, 2026-10-05). New code: imports no earlier script and no GPT code.
Usage: PYTHONDONTWRITEBYTECODE=1 python3 r3_checks.py SECTION [args]
  S1  Stone's (x+x^8+x^16)^3 vs P_{5,3}; TIT App. P_{e,t} branch values (algebra check)
  S2  Theorem A/B: sparse identities m<=101, gcd(g,E) for s<=SMAX, dense g-adic valuation m<=11, field checks m<=13
  S3  Theorem C, Lemma P (Gold + linear permutations), cyclotomic classes, F_2-linear census
  S4  Lemma M on the Frobenius-inner untwisted family (all lambda, all k), m = 5..15
  S5  twists from function tables: |U|, disjointness, degrees, cyclic width; arg: m list
Writes r3_<SECTION>.json; prints PASS/FAIL lines; exit 1 on any FAIL.
"""
import sys; sys.dont_write_bytecode = True
import json, random
from math import gcd
from collections import Counter
import numpy as np

FAILS = []
def check(cond, msg):
    print(('PASS ' if cond else 'FAIL ') + msg, flush=True)
    if not cond: FAILS.append(msg)
    return cond

# ---------------- F_2[X] on Python ints ----------------
def pmod(a, b):
    db = b.bit_length()
    while a and a.bit_length() >= db:
        a ^= b << (a.bit_length() - db)
    return a
def pgcd(a, b):
    while b:
        a, b = b, pmod(a, b)
    return a
def pmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r

# ---------------- GF(2^m) ----------------
class GF:
    def __init__(self, m, which=0):
        self.m = m; q = self.q = 1 << m; Q = self.Q = q - 1
        found = 0
        for p in range((1 << (m + 1)) - 1, 1 << m, -2):     # largest-first: differs from earlier code's moduli
            x = 1; per = 0
            while True:
                x <<= 1
                if x >> m: x ^= p
                per += 1
                if x == 1 or per > Q: break
            if per == Q:
                if found == which: break
                found += 1
        self.poly = p
        e = np.zeros(2 * Q, dtype=np.int64); x = 1
        for i in range(Q):
            e[i] = x; x <<= 1
            if x >> m: x ^= p
        e[Q:] = e[:Q]
        self.exp = e
        lg = np.zeros(q, dtype=np.int64); lg[e[:Q]] = np.arange(Q); self.log = lg
        self.xs = np.arange(q, dtype=np.int64)
        self.tr = np.zeros(q, dtype=np.int64)
        for i in range(m): self.tr ^= self.pw(1 << i)
        assert set(np.unique(self.tr).tolist()) <= {0, 1}
    def pw(self, e):
        """table x -> x^e, e >= 1"""
        v = np.zeros(self.q, dtype=np.int64)
        v[1:] = self.exp[(self.log[1:] * (e % self.Q)) % self.Q]
        if e % self.Q == 0: v[1:] = 1
        return v
    def mul(self, a, b):
        a = np.asarray(a); b = np.asarray(b)
        r = self.exp[(self.log[a] + self.log[b]) % self.Q]
        return np.where((a == 0) | (b == 0), 0, r)
    def poly_vals(self, exps):
        v = np.zeros(self.q, dtype=np.int64)
        for e in exps:
            if e == 0: v ^= 1
            else: v ^= self.pw(e)
        return v

def ranks_all(cols, m):
    """cols: list of m int arrays; returns rank of {cols[l][a]} for each a (vectorised xor basis)."""
    N = cols[0].shape[0]
    basis = np.zeros((m, N), dtype=np.int64)
    for v0 in cols:
        v = v0.copy()
        for b in range(m - 1, -1, -1):
            has = ((v >> b) & 1).astype(bool)
            emp = basis[b] == 0
            ins = has & emp
            basis[b][ins] = v[ins]; v[ins] = 0
            red = has & ~emp
            v[red] ^= basis[b][red]
    return (basis != 0).sum(axis=0)

def du_quadratic(F, vals):
    """exact differential uniformity of a quadratic function given by its value table"""
    m, q = F.m, F.q
    a = np.arange(1, q)
    cols = [vals[a ^ (1 << l)] ^ vals[a] ^ vals[1 << l] ^ vals[0] for l in range(m)]
    rk = ranks_all(cols, m)
    return 1 << (m - int(rk.min()))

def is_perm(v): return np.unique(v).size == v.size

# ======================= S1 =======================
def S1():
    out = {}
    # Stone: (x + x^8 + x^16)^3 on F_32, reduced mod x^32 - x
    C = Counter()
    base = [1, 8, 16]
    for a in base:
        for b in base:
            C[2 * a + b] += 1          # (.)^2 * (.)
    exps = set()
    for e, c in C.items():
        if c % 2:
            while e >= 32: e -= 31
            exps ^= {e}
    m, r = 5, 3
    P53 = P_support(m, r)
    out['stone_reduced'] = sorted(exps); out['P53'] = sorted(P53)
    check(exps == P53, 'S1 Stone (x+x^8+x^16)^3 reduced == P_{5,3} as polynomials: %s' % sorted(exps, reverse=True))
    # Field check of the same (independent of exponent arithmetic)
    F = GF(5)
    L = F.pw(1) ^ F.pw(8) ^ F.pw(16)
    stone = F.pw(3)[L]
    check(np.array_equal(stone, F.poly_vals(P53)), 'S1 Stone function == P_{5,3} on F_32 (value tables)')
    # TIT App. thm:gold: P_{e,t}' = t (X^{2^e}+X+1)^2 ; branch values R(alpha) = alpha^4 + alpha^2 at roots of X^{2^e}+X+1
    # algebra: alpha^{2^e} = alpha + 1 => alpha^{2^{e+1}+2} = alpha^4 + alpha^2 ; count distinct values over the 2^e roots
    res = {}
    for e in (2, 3, 4, 5, 6):
        s = e; G2 = GF(2 * s)          # roots of X^{2^s}+X+1 lie in F_{2^{2s}}
        gv = G2.pw(1 << s) ^ G2.xs ^ 1
        roots = np.nonzero(gv == 0)[0]
        Rv = G2.pw((1 << (e + 1)) + 2)[roots]
        alt = G2.pw(4)[roots] ^ G2.pw(2)[roots]
        res[e] = dict(roots=int(roots.size), distinct_branch_values=int(np.unique(Rv).size))
        check(roots.size == (1 << s) and np.array_equal(Rv, alt) and np.unique(Rv).size == (1 << (e - 1)),
              'S1 TIT P_{e,t}: e=%d, %d roots of X^{2^e}+X+1, R(alpha)=alpha^4+alpha^2 takes %d distinct values' % (e, roots.size, np.unique(Rv).size))
    out['tit_branch_values'] = res
    return out

# ======================= S2 =======================
def admissible(m):
    return [r for r in range(3, m, 2) if gcd(r, m) == 1]
def P_support(m, r):
    C = Counter()
    for i in range(r):
        for j in range(r):
            C[(1 << (i + 1)) + (1 << j)] += 1
    T3 = {e for e, c in C.items() if c % 2}
    Q = (1 << m) - 1
    S = {(e << (m - 2)) % Q for e in T3}
    assert 0 not in S
    return S
def S2(smax=14):
    out = {}
    npairs = 0; bad = []
    for m in range(5, 102, 2):
        for r in admissible(m):
            npairs += 1
            S = P_support(m, r)
            ok = len(S) == 3 * r - 2 and max(S) == 3 << (m - 2)
            der = {e - 1 for e in S if e & 1}
            ok &= der == {0, 1 << (r - 2), 1 << (m - 2)}
            D = [0, 1 << (r - 2), 1 << (m - 2)]
            E = [0] + [1 << i for i in range(r - 2)] + [1 << (m - 2), 1 << (m - 1)]
            ok &= len(set(E)) == len(E)
            Z = Counter()
            for a in D:
                for b in E: Z[a + b] += 1
            Z[0] -= 1; Z[1 << (m - 2)] -= 2; Z[1 << (m - 1)] -= 2
            Z = {e: c for e, c in Z.items() if c}
            ok &= Z == {e: 1 for e in S}
            if not ok: bad.append((m, r))
    check(not bad, 'S2 Theorem A support (3r-2 terms, deg 3q/4), P\' = 1+W+Y, Z[X] identity P^ = DE-1-2(Y+Z): %d admissible pairs m<=101, bad=%s' % (npairs, bad[:5]))
    out['sparse_pairs'] = npairs
    # gcd(g, E) = 1, E == 1 + T_r mod g, for s = m - r <= smax
    def f(e, s):            # X^{2^e} mod g, g = X^{2^s}+X+1
        k = 0
        while e >= s: e -= s; k ^= 1
        return (1 << (1 << e)) ^ k
    ng = 0; badg = []
    for m in range(5, 102, 2):
        for r in admissible(m):
            s = m - r
            if s > smax: continue
            ng += 1
            g = (1 << (1 << s)) | 3
            Em = 1 ^ f(m - 2, s) ^ f(m - 1, s)
            for i in range(r - 2): Em ^= f(i, s)
            Tm = 1
            for i in range(r): Tm ^= f(i, s)
            Em = pmod(Em, g); Tm = pmod(Tm, g)
            if not (Em == Tm and pgcd(g, Em) == 1 and pgcd(g, Tm) == 1): badg.append((m, r))
    check(not badg, 'S2 Theorem B: E == 1+T_r mod g and gcd(g,E)=1 for %d pairs (m<=101, s<=%d), bad=%s' % (ng, smax, badg[:5]))
    out['gcd_pairs'] = ng; out['smax'] = smax
    # dense g-adic valuation of P+1 (no use of the product identity), m <= 11
    nv = 0; badv = []
    for m in range(5, 12, 2):
        for r in admissible(m):
            s = m - r; t = 1 << (r - 2)
            g = (1 << (1 << s)) | 3
            A = 1
            for e in P_support(m, r): A ^= 1 << e
            v = 0
            while True:
                qq, rr = pdivmod(A, g)
                if rr: break
                A = qq; v += 1
            nv += 1
            if v != t: badv.append((m, r, v, t))
    check(not badv, 'S2 Theorem B: ord_g(P+1) = t = 2^{r-2} exactly, by repeated division, %d pairs m<=11, bad=%s' % (nv, badv))
    # field checks
    fc = {}
    for m in (5, 7, 9, 11, 13):
        F = GF(m)
        for r in admissible(m):
            S = P_support(m, r)
            v = F.poly_vals(S)
            dv = F.poly_vals([0, 1 << (r - 2), 1 << (m - 2)])      # P'
            Ev = F.poly_vals([0] + [1 << i for i in range(r - 2)] + [1 << (m - 2), 1 << (m - 1)])
            gv = F.pw(1 << (m - r)) ^ F.xs ^ 1
            perm = is_perm(v); du = du_quadratic(F, v)
            cnt = np.bincount(dv, minlength=F.q)
            opt = cnt[0] == 0 and set(np.unique(cnt[cnt > 0]).tolist()) == {2}
            x0 = np.nonzero(v == 1)[0]
            ok = perm and du == 2 and opt and x0.size == 1 and Ev[x0[0]] == 0 and (gv != 0).all()
            ok &= np.array_equal(v ^ 1, F.mul(dv, Ev))          # P+1 = P'E as functions
            fc['%d,%d' % (m, r)] = dict(perm=bool(perm), du=int(du), opt=bool(opt), ok=bool(ok))
            check(ok, 'S2 field m=%d r=%d: perm, DU=%d, opt, unique root of P=1 is a root of E, g has no F_q root, P+1=P\'E' % (m, r, du))
    out['field'] = fc
    # Riemann-Hurwitz bookkeeping for P: P^1 -> P^1, n = 3q/4
    rh = []
    for m in range(5, 40, 2):
        for r in admissible(m):
            q = 1 << m; n = 3 * q // 4; s = m - r; t = 1 << (r - 2)
            deg_der = 1 << (m - 2)
            d_inf = 2 * n - 2 - deg_der
            rh.append(d_inf == 5 * q // 4 - 2 and (1 << s) * t == deg_der and d_inf >= n)
    check(all(rh), 'S2 Riemann-Hurwitz: finite different exponents t at 2^s points (sum 2^{m-2} = deg P\'), d_inf = 5q/4 - 2 >= e_inf = 3q/4')
    return out
def pdivmod(a, b):
    db = b.bit_length(); qq = 0
    while a and a.bit_length() >= db:
        sh = a.bit_length() - db
        qq ^= 1 << sh; a ^= b << sh
    return qq, a

# ======================= S3 =======================
def S3():
    out = {}
    # (a) L1 = y + y^2 + y^{2^c} bijective iff 3 does not divide m
    bad = []
    for m in range(5, 302, 2):
        c = (m + 1) // 2
        unit = pgcd((1 << m) | 1, (1 << c) | 3) == 1
        if unit != (m % 3 != 0): bad.append(m)
    check(not bad, 'S3 gcd(1+t+t^c, t^m-1)=1 iff 3 does not divide m, odd m in [5,301], bad=%s' % bad)
    # (b) D_m, Q_m = D_m + X on fields
    fam = {}
    for m in (5, 7, 9, 11, 13, 15):
        F = GF(m); k = (m - 1) // 2; c = (m + 1) // 2
        D = F.poly_vals([(1 << k) + 1, (1 << (k + 1)) + 2, (1 << c) + 1])
        G = F.pw((1 << k) + 1)
        L1 = F.xs ^ F.pw(2) ^ F.pw(1 << c)
        comp = np.array_equal(D, L1[G])
        du = du_quadratic(F, D)
        Qv = D ^ F.xs
        dQ = F.poly_vals([0, 1 << k, 1 << c])
        cnt = np.bincount(dQ, minlength=F.q)
        opt = bool(cnt[0] == 0 and set(np.unique(cnt[cnt > 0]).tolist()) == {2})
        fam[m] = dict(D_is_L1_of_Gold=bool(comp), DU_exact=int(du), D_perm=bool(is_perm(D)),
                      L1_bijective=bool(is_perm(L1)), Q_opt=opt, Q_perm=bool(is_perm(Qv)),
                      Q0_eq_Q1=bool(Qv[0] == Qv[1]), degree=(1 << c) + 2)
        exp_apn = (m % 3 != 0)
        check(comp and (du == 2) == exp_apn and fam[m]['D_perm'] == exp_apn and opt and not fam[m]['Q_perm'] and fam[m]['Q0_eq_Q1'],
              'S3 m=%d: D_m = L1(Gold), DU=%d (exact), D_m perm=%s, Q_m=D_m+X opt=%s, Q_m perm=%s, Q(0)=Q(1)' %
              (m, du, fam[m]['D_perm'], opt, fam[m]['Q_perm']))
    out['family'] = fam
    # (c) Lemma P: x^{2^k+1} + M(x) (M F_q-linear) permutes F_q iff M = c^{2^k} x + c x^{2^k}
    lp = {}
    for m in (5, 7, 9, 11, 13):
        F = GF(m); Q = F.Q; a = np.arange(1, F.q)
        for k in range(1, m):
            if gcd(k, m) != 1: continue
            vecs = []
            for i in range(m):
                ai = F.exp[(F.log[a] * (((1 << i) - (1 << k) - 1) % Q)) % Q]
                for b in range(m):
                    fv = F.tr[F.mul(np.full(a.size, 1 << b), ai)]
                    vecs.append(int.from_bytes(np.packbits(fv.astype(np.uint8)).tobytes(), 'big'))
            basis = {}
            for v in vecs:
                while v:
                    h = v.bit_length() - 1
                    if h in basis: v ^= basis[h]
                    else: basis[h] = v; break
            kdim = m * m - len(basis)
            lp['%d,%d' % (m, k)] = kdim
            check(kdim == m, 'S3 Lemma P m=%d k=%d: dim_F2 {M : Tr(M(a)/a^(2^k+1)) = 0 for all a != 0} = %d (translations: %d)' % (m, k, kdim, m))
        # spot-check criterion <=> permutation, k = (m-1)/2
        k = (m - 1) // 2; G = F.pw((1 << k) + 1); rng = random.Random(m)
        okc = True
        for trial in range(12):
            if trial < 4:
                cc = rng.randrange(1, F.q)
                coef = {0: int(F.mul(F.pw(1 << k)[cc], 1)), k: cc}
            else:
                coef = {i: rng.randrange(F.q) for i in range(m)}
            M = np.zeros(F.q, dtype=np.int64)
            for i, ci in coef.items(): M ^= F.mul(np.full(F.q, ci), F.pw(1 << i))
            crit = bool((F.tr[F.mul(M[1:], F.exp[(-F.log[1:] * ((1 << k) + 1)) % Q])] == 0).all())
            okc &= crit == is_perm(G ^ M)
            if trial < 4: okc &= crit
        check(okc, 'S3 Lemma P m=%d: criterion == permutation on 4 translations + 8 random M' % m)
    out['lemmaP_kernel_dims'] = lp
    # (d) cyclotomic classes of e_i = 2^i - 2^k - 1, m <= 61, all k coprime
    badc = []; n = 0
    for m in range(5, 62, 2):
        Q = (1 << m) - 1
        def rots(e): return {((e << j) | (e >> (m - j))) & Q for j in range(m)}
        for k in range(1, m):
            if gcd(k, m) != 1: continue
            n += 1
            cl = []
            for i in range(m):
                e = ((1 << i) - (1 << k) - 1) % Q
                R = rots(e)
                if e == 0 or len(R) != m: badc.append((m, k, i, 'size')); break
                cl.append(min(R))
            ok = cl[0] == cl[k] and len(set(cl)) == m - 1
            if not ok: badc.append((m, k))
    check(not badc, 'S3 cyclotomic classes: e_0 ~ e_k, all other classes distinct, all of size m, %d (m,k) pairs m<=61, bad=%s' % (n, badc[:5]))
    # (e) census of F_2-linear L with D_m + L a permutation
    cen = {}
    for m in (5, 7, 11, 13):
        F = GF(m); k = (m - 1) // 2; c = (m + 1) // 2
        D = F.poly_vals([(1 << k) + 1, (1 << (k + 1)) + 2, (1 << c) + 1])
        lin = [F.pw(1 << i) for i in range(m)]
        hits = []
        for mask in range(1 << m):
            v = D.copy()
            for i in range(m):
                if mask >> i & 1: v ^= lin[i]
            if is_perm(v): hits.append(sorted(i for i in range(m) if mask >> i & 1))
        # prediction: L in {0, L1(x + x^{2^k})} ; L1(x+x^{2^k}) = sum over y, y^2, y^{2^c} of x and x^{2^k}
        Cc = Counter([0, k, 1, k + 1, c % m, (k + c) % m])
        pred = sorted(i for i, cnt in Cc.items() if cnt % 2)
        cen[m] = dict(hits=hits, predicted_nonzero=pred)
        check(sorted(map(tuple, hits)) == sorted([(), tuple(pred)]),
              'S3 census m=%d: F_2-linear L with D_m+L perm are exactly {0, %s}; none contains X' % (m, ['X^%d' % (1 << i) for i in pred]))
    out['census'] = cen
    return out

# ======================= S4 =======================
def S4():
    out = {}
    for m in range(5, 16, 2):
        T = (1 << m) | 1; e = (m - 1) // 2; bound = 1 << ((m + 1) // 2)
        viol = 0; best_unit = None; best_any = None; cancel = 0; nopt = 0
        for lam in range(1, 1 << m):
            unit = pgcd(T, lam) == 1
            cs = [c for c in range(m) if lam >> c & 1]
            for k in range(1, m):
                if gcd(k, m) != 1: continue
                sup = set()
                for c in cs:
                    p = frozenset((c, (c + k) % m))
                    sup ^= {p}
                if len(sup) != len(cs): cancel += 1
                deg = max((1 << a) + (1 << b) for a, b in (tuple(p) for p in sup))
                K = 0
                for p in sup:
                    if 0 in p: K ^= 1 << max(p)
                if pgcd(T, K) != 3: continue
                nopt += 1
                if deg < bound: viol += 1
                if best_any is None or deg < best_any[0]: best_any = (deg, lam, k)
                if unit and (best_unit is None or deg < best_unit[0]): best_unit = (deg, lam, k)
        out[m] = dict(opt_forms=nopt, cancellations=cancel, violations_below_2c=viol,
                      min_deg_opt_unit=best_unit, min_deg_opt_any=best_any, bound_2c=bound, Dm_degree=bound + 2)
        check(cancel == 0 and viol == 0,
              'S4 Lemma M m=%d: no cancellation; no opt form below 2^{(m+1)/2}=%d; min opt degree (lambda unit) = %s' % (m, bound, best_unit and best_unit[0]))
    return out

# ======================= S5 =======================
def units(m):
    T = (1 << m) | 1
    return [l for l in range(1, 1 << m) if pgcd(T, l) == 1]
def normal_basis(F, skip=0):
    found = 0
    for b in range(1, F.q):
        conj = [int(F.pw(1 << i)[b]) for i in range(F.m)]
        basis = {}
        for v in conj:
            while v:
                h = v.bit_length() - 1
                if h in basis: v ^= basis[h]
                else: basis[h] = v; break
        if len(basis) == F.m:
            if found == skip: return conj
            found += 1
def coord_tables(F, conj):
    m, q = F.m, F.q
    fromc = np.zeros(q, dtype=np.int64)
    for cv in range(1, q):
        x = 0
        for i in range(m):
            if cv >> i & 1: x ^= conj[i]
        fromc[cv] = x
    toc = np.zeros(q, dtype=np.int64); toc[fromc] = np.arange(q)
    return fromc, toc
def Mu_table(F, fromc, toc, u):
    m = F.m
    cv = toc[F.xs]; nv = np.zeros_like(cv)
    for i in range(m):
        nv |= ((cv >> i) & 1) << ((u * i) % m)
    return fromc[nv]
def S5(ms):
    out = {}
    for m in ms:
        F = GF(m); q = F.q; Q = F.Q
        U = units(m)
        lt = {}
        for l in U:
            v = np.zeros(q, dtype=np.int64)
            for i in range(m):
                if l >> i & 1: v ^= F.pw(1 << i)
            lt[l] = v
        Ntabs = np.stack([lt[l] for l in U])
        pairs = [(i, j) for i in range(m) for j in range(i + 1, m)]
        pi = np.array([1 << i for i, j in pairs]); pj = np.array([1 << j for i, j in pairs])
        def keys(Fv):        # Fv: (n, q) -> bilinear-form keys
            B = Fv[:, pi ^ pj] ^ Fv[:, pi] ^ Fv[:, pj] ^ Fv[:, [0]]
            return [row.tobytes() for row in B]
        seen = {}
        for k in range(1, m):
            if gcd(k, m) != 1: continue
            G = F.pw((1 << k) + 1)
            for l in U:
                Fv = Ntabs[:, G[lt[l]]]
                for kk, row in zip(keys(Fv), Fv):
                    if kk not in seen: seen[kk] = row
        Ukeys = list(seen.keys()); Uf = np.stack([seen[kk] for kk in Ukeys])
        doexps = [((1 << i) + (1 << j), i, j) for i, j in pairs]
        logx = F.log[1:]
        def do_support(Fv):
            """returns list of DO supports (list of (i,j)) and an all-F2 flag"""
            sup = [[] for _ in range(Fv.shape[0])]; f2 = True
            for st in range(0, Fv.shape[0], 2000):
                blk = Fv[st:st + 2000, 1:]
                nz = blk != 0
                lb = F.log[blk]
                for e, i, j in doexps:
                    val = np.where(nz, F.exp[(lb - e * logx) % Q], 0)
                    cvec = np.bitwise_xor.reduce(val, axis=1)
                    if ((cvec != 0) & (cvec != 1)).any(): f2 = False
                    for t in np.nonzero(cvec)[0]: sup[st + t].append((i, j))
            return sup, f2
        def deg(s): return max((1 << i) + (1 << j) for i, j in s)
        def width(s): return min(max(max((i + a) % m, (j + a) % m) for i, j in s) for a in range(m))
        res = dict(U=len(Ukeys))
        twist_sets = {}; mins = {}
        for basis_skip in (0, 1) if m <= 7 else (0,):
            conj = normal_basis(F, basis_skip); fromc, toc = coord_tables(F, conj)
            for u in range(1, m):
                if gcd(u, m) != 1: continue
                Mu = Mu_table(F, fromc, toc, u); Mi = Mu_table(F, fromc, toc, pow(u, -1, m))
                assert np.array_equal(Mu[Mi], F.xs)
                Tv = Mu[Uf[:, Mi]]
                ks = set(keys(Tv))
                if basis_skip == 0:
                    twist_sets[u] = ks
                    sup, f2 = do_support(Tv)
                    ds = [deg(s) for s in sup]; ws = [width(s) for s in sup]
                    mins[u] = dict(size=len(ks), F2=f2, min_deg=min(ds), n_deg_le_2m2=sum(d <= (1 << (m - 2)) for d in ds),
                                   min_width=min(ws), max_width=max(ws))
                else:
                    check(ks == twist_sets[u], 'S5 m=%d u=%d: twist set independent of the normal basis' % (m, u))
        allk = [twist_sets[u] for u in twist_sets]
        disj = sum(len(s) for s in allk) == len(set().union(*allk))
        res['twists'] = {str(u): v for u, v in mins.items()}; res['disjoint'] = disj
        check(twist_sets[1] == set(Ukeys), 'S5 m=%d: u=1 twist set == U' % m)
        tw = [mins[u] for u in mins if u != 1]
        check(disj and all(t['F2'] for t in mins.values()) and all(t['size'] == len(Ukeys) for t in mins.values()),
              'S5 m=%d: |U|=%d, %d twist sets of equal size, pairwise disjoint, all coefficients in F_2' % (m, len(Ukeys), len(mins)))
        check(all(t['n_deg_le_2m2'] == 0 for t in tw),
              'S5 m=%d: twisted (u!=1) min degree %d > 2^{m-2}=%d; min cyclic width twisted %d, untwisted %d' %
              (m, min(t['min_deg'] for t in tw), 1 << (m - 2), min(t['min_width'] for t in tw), mins[1]['min_width']))
        out[m] = res
    return out

if __name__ == '__main__':
    sec = sys.argv[1]
    if sec == 'S1': r = S1()
    elif sec == 'S2': r = S2(int(sys.argv[2]) if len(sys.argv) > 2 else 14)
    elif sec == 'S3': r = S3()
    elif sec == 'S4': r = S4()
    elif sec == 'S5': r = S5([int(x) for x in sys.argv[2:]] or [5, 7])
    json.dump(dict(section=sec, result=r, fails=FAILS), open('r3_%s.json' % sec, 'w'), indent=1, default=str)
    print('SECTION %s: %s' % (sec, 'FAIL %d' % len(FAILS) if FAILS else 'ALL PASS'))
    sys.exit(1 if FAILS else 0)
