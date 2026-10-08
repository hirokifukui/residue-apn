"""main_checks.py -- checks for the R5 main paper that are not in r3_checks.py / thmA.py / ring.py (Claude, 2026-10-06; new code).
Imports nothing but the standard library and NumPy.  Usage: python3 -I main_checks.py SECTION
  C1  Remark 4.2: (X^2+X+1)^2 ((X+1)^2 + T) = X^6 + 1 + (X^4+X^2+1) T in F_2[X][T]  (the e = 1 factorisation),
      and the number of finite branch values (a^2+a)^2 over the roots a of X^{2^e}+X+1 is 2^{e-1}, e = 1..6.
  C2  Theorem 6.2 / Proposition 6.1 on GR(2^k,5), k = 2, 3: the natural lift of P_{5,3} and one random coefficient lift
      (P_{5,3} + 2*random polynomial of degree <= 40): permutation; unit rows off rho equal the residue rows; top-ideal rows have
      all nonzero entries 2q^{k-1}; every row maximum <= 2q^{k-1}; Delta_F = 2q^{k-1}; row maxima over rho reported.
  C3  Proposition 7.1 for P_{m,m-2}, m = 5, 7: normalisation (rho = 1, image of the 1-difference = {Tr = 1}, checked directly),
      every admissible (a,b): no forbidden two-layer transition; control: random invertible 2x2 matrices do allow one.
Writes main_<SECTION>.json; prints PASS/FAIL lines; exit 1 on any FAIL."""
import sys; sys.dont_write_bytecode = True
import json, random
import numpy as np

FAILS = []; OUT = {}
def check(cond, msg):
    print(('PASS ' if cond else 'FAIL ') + msg, flush=True)
    if not cond: FAILS.append(msg)
    return cond

# ---------- F_2[X] on ints ----------
def pmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def is_irred(p):
    dg = p.bit_length() - 1
    for d in range(2, 1 << (dg // 2 + 1)):
        if d.bit_length() - 1 > dg // 2: break
        a = p
        while a and a.bit_length() >= d.bit_length(): a ^= d << (a.bit_length() - d.bit_length())
        if a == 0: return False
    return True

class GF:
    """GF(2^m) by an irreducible polynomial found by search (any irreducible works for these checks)"""
    def __init__(self, m):
        self.m = m; self.q = q = 1 << m
        self.p = next(p for p in range(q + 1, 2 * q, 2) if is_irred(p))
    def mul(self, a, b):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a & self.q: a ^= self.p
        return r
    def pw(self, a, e):
        r = 1
        while e:
            if e & 1: r = self.mul(r, a)
            a = self.mul(a, a); e >>= 1
        return r
    def tr(self, a):
        s = 0; x = a
        for _ in range(self.m): s ^= x; x = self.mul(x, x)
        return s

def C1():
    # polynomial identity in F_2[X][T]: write A + B*T; left = g^2 (X^2+1) + g^2 T, right = X^6+1 + (X^4+X^2+1) T
    g2 = pmul(0b111, 0b111)
    check(g2 == 0b10101, 'C1 (X^2+X+1)^2 = X^4+X^2+1')
    check(pmul(g2, 0b101) == (1 << 6) | 1, 'C1 (X^4+X^2+1)(X^2+1) = X^6+1, hence P_{1,t}+1 = (X^2+X+1)^2((X+1)^2+T_t)')
    res = {}
    for e in range(1, 7):
        F = GF(2 * e)           # the roots of X^{2^e}+X+1 lie in F_{2^{2e}}
        roots = [a for a in range(F.q) if F.pw(a, 1 << e) ^ a ^ 1 == 0]
        vals = {F.mul(F.mul(a, a) ^ a, F.mul(a, a) ^ a) for a in roots}
        vals2 = {F.pw(a, (1 << (e + 1)) + 2) for a in roots}
        res[e] = [len(roots), len(vals)]
        check(len(roots) == 1 << e and vals == vals2 and len(vals) == 1 << (e - 1),
              'C1 e=%d: %d roots of X^{2^e}+X+1, alpha^{2^{e+1}+2} = (alpha^2+alpha)^2, %d distinct values (2^{e-1} = %d)'
              % (e, len(roots), len(vals), 1 << (e - 1)))
    OUT['C1'] = res

# ---------- Galois ring GR(2^k,5) = Z_{2^k}[x]/(x^5+x^2+1) ----------
def P_terms(m, r):
    from collections import Counter
    q = 1 << m; c = Counter()
    for i in range(r):
        for j in range(r): c[2 ** (i + 1) + 2 ** j] += 1
    T3 = {e for e, v in c.items() if v % 2}
    c2 = Counter()
    for e in T3:
        f = (e * 2 ** (m - 2)) % (q - 1)
        c2[q - 1 if f == 0 else f] += 1
    return sorted(e for e, v in c2.items() if v % 2)

def C2():
    m = 5; q = 32; P = P_terms(5, 3)
    check(len(P) == 3 * 3 - 2 and max(P) == 3 * q // 4, 'C2 P_{5,3} has 3r-2 = 7 terms and degree 3q/4 = 24: %s' % P)
    rng = random.Random(20261006)
    res = {}
    for k in (2, 3):
        Nn = 1 << k; n = Nn ** m
        idx = np.arange(n); dig = np.stack([(idx // Nn ** i) % Nn for i in range(m)], 1)
        Wt = Nn ** np.arange(m)
        def enc(dd): return (dd % Nn) @ Wt
        def mul(a, b):
            c = np.zeros((a.shape[0], 2 * m - 1), dtype=np.int64)
            for i in range(m):
                for j in range(m): c[:, i + j] += a[:, i] * b[:, j]
            for t in range(2 * m - 2, m - 1, -1):
                co = c[:, t].copy(); c[:, t] = 0; c[:, t - 5] -= co; c[:, t - 3] -= co
            return c[:, :m] % Nn
        # powers x^e, e = 0..40
        pw = [np.zeros_like(dig)]; pw[0][:, 0] = 1
        for e in range(1, 41): pw.append(mul(pw[-1], dig))
        # residue (field) values: GF(32) by the same modulus
        resid = dig % 2
        def ring_eval(coef):          # coef: dict e -> element of R given as length-5 digit vector
            s = np.zeros_like(dig)
            for e, cv in coef.items():
                s = (s + mul(pw[e], np.broadcast_to(np.array(cv), dig.shape).copy())) % Nn
            return s
        natural = {e: [1, 0, 0, 0, 0] for e in P}
        rnd = {e: [0] * 5 for e in range(41)}
        for e in range(41):
            rnd[e] = [2 * rng.randrange(Nn // 2) for _ in range(5)]
            if e in P: rnd[e][0] += 1
        # field function p on residues: evaluate natural lift at k-digit 0/1 inputs and reduce mod 2
        fld_idx = enc(resid)                      # index of the 0/1 representative
        for name, coef in (('natural', natural), ('random_lift', rnd)):
            Fv = ring_eval(coef); Fi = enc(Fv)
            perm = len(np.unique(Fi)) == n
            Fd = Fv
            # residue function as table on 0..31 (bit i = digit i mod 2)
            rbits = (Fv % 2) @ (2 ** np.arange(m))
            xbits = resid @ (2 ** np.arange(m))
            pf = np.zeros(q, dtype=np.int64); pf[xbits] = rbits
            # rho: kernel of p' -- p' = 1 + x^{2^{r-2}} + x^{2^{m-2}} has fibres {x, x+1}: rho = 1 (bit 0)
            rho = 1
            stats = dict(unit_off_rho_ok=True, top_ok=True, rowmax_le=True, max_rho=0, max_2R_not_top=0, Delta=0)
            for a in range(1, n):
                da = dig[a]; abar = int((da % 2) @ (2 ** np.arange(m)))
                xi = enc(dig + da); d = enc(Fd[xi] - Fd)
                cnt = np.bincount(d, minlength=n); mx = int(cnt.max())
                stats['Delta'] = max(stats['Delta'], mx)
                if mx > 2 * q ** (k - 1): stats['rowmax_le'] = False
                if abar not in (0, rho):
                    # compare with residue row: delta_F(a,b) = #{y : p(y+abar)+p(y) = bbar}
                    frow = np.bincount(pf[np.arange(q) ^ abar] ^ pf, minlength=q)
                    bbar = (dig % 2) @ (2 ** np.arange(m))
                    if not np.array_equal(cnt, frow[bbar]): stats['unit_off_rho_ok'] = False
                elif abar == rho:
                    stats['max_rho'] = max(stats['max_rho'], mx)
                else:
                    top = bool(np.all(da % (Nn // 2) == 0))
                    if top:
                        nz = cnt[cnt > 0]
                        if not np.all(nz == 2 * q ** (k - 1)): stats['top_ok'] = False
                    else:
                        stats['max_2R_not_top'] = max(stats['max_2R_not_top'], mx)
            res['%s_k%d' % (name, k)] = dict(perm=perm, **stats)
            check(perm and stats['unit_off_rho_ok'] and stats['top_ok'] and stats['rowmax_le'] and stats['Delta'] == 2 * q ** (k - 1),
                  'C2 %s k=%d: permutation, unit rows off rho = residue rows, top-ideal entries 2q^(k-1), Delta_F = %d = 2q^(k-1); max over rho %d, max in 2R minus top %s'
                  % (name, k, stats['Delta'], stats['max_rho'], stats['max_2R_not_top'] if k > 2 else '-'))
    OUT['C2'] = res

def C3():
    res = {}
    for m in (5, 7):
        F = GF(m); q = F.q; r = m - 2
        P = P_terms(m, r)
        p = np.array([0] * q, dtype=np.int64)
        for x in range(q):
            v = 0
            for e in P: v ^= F.pw(x, e)
            p[x] = v
        TR = np.array([F.tr(x) for x in range(q)])
        d1 = set((p[np.arange(q) ^ 1] ^ p).tolist())
        check(d1 == set(np.nonzero(TR == 1)[0].tolist()) and len(set(p.tolist())) == q,
              'C3 m=%d: P_{m,m-2} permutation, rho = 1, {P(y+1)+P(y)} = {Tr = 1} (no scaling needed)' % m)
        img = {a: set((p[np.arange(q) ^ a] ^ p).tolist()) for a in (0, 1)}
        MUL = np.array([[F.mul(a, b) for b in range(q)] for a in range(q)], dtype=np.int64)
        INV = [0] + [next(b for b in range(1, q) if MUL[a, b] == 1) for a in range(1, q)]
        def forbidden(M):
            for al in ((0, 1), (1, 0), (1, 1)):
                for b0 in img[al[0]]:
                    for b1 in img[al[1]]:
                        n0 = MUL[M[0][0], b0] ^ MUL[M[0][1], b1]; n1 = MUL[M[1][0], b0] ^ MUL[M[1][1], b1]
                        if (n0, n1) != (0, 0) and n0 in (0, 1) and n1 in (0, 1): return True
            return False
        T0 = [x for x in range(1, q) if TR[x] == 0]
        tot = bad = 0
        for a in T0:
            for b in T0:
                if a == b: continue
                det = MUL[a, a ^ b] ^ MUL[b, b]; di = INV[det]
                M = [[MUL[a ^ b, di], MUL[b, di]], [MUL[b, di], MUL[a, di]]]
                tot += 1
                if forbidden(M): bad += 1
        rng = random.Random(m); ctl = 0; N = 200
        for _ in range(N):
            while True:
                M = [[rng.randrange(q) for _ in range(2)] for _ in range(2)]
                if MUL[M[0][0], M[1][1]] ^ MUL[M[0][1], M[1][0]]: break
            if forbidden(M): ctl += 1
        res[m] = dict(pairs=tot, failing=bad, random_invertible_allowing=ctl, random_N=N)
        check(bad == 0 and tot == len(T0) * (len(T0) - 1), 'C3 m=%d: all %d admissible (a,b): no forbidden two-layer transition' % (m, tot))
        check(ctl > 0, 'C3 m=%d control: %d of %d random invertible M allow such a transition (the statement is not vacuous)' % (m, ctl, N))
    OUT['C3'] = res

if __name__ == '__main__':
    sec = sys.argv[1]
    {'C1': C1, 'C2': C2, 'C3': C3}[sec]()
    json.dump(OUT, open('main_%s.json' % sec, 'w'), indent=1, default=str)
    sys.exit(1 if FAILS else 0)
