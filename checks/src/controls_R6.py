"""controls_R6.py -- R6 controls for the main paper (Claude, 2026-10-07; new code, standard library only).
C4a  fixed polynomial: P_{5,3} = X+X^2+X^3+X^9+X^10+X^18+X^24 evaluated on F_{2^7} (x^7+x+1) is NOT a permutation,
     while P_{7,3}, P_{7,5} (the family member for m = 7) are (Thm 3.1 builds P_{m,r} anew for every m).
C4b  Remark 4.2: P_{e,t} = X^(2^(e+1)+2) + (X^(2^(e+1))+X^2+1) T_t on F_{2^9} (x^9+x^4+1), t = x (code 2), Tr t = 0.
     e = 3 (gcd(e,9) = 3): expected permutation, DU 8, P' zero-free, nonempty fibres of P' of size 8 -- not APN, not opt.
     e = 2, 4 (gcd 1): expected permutation, DU 2, zero-free, fibres 2 (optimal APN permutation, as in [TIT]).
     For every e = 1..4 the finite branch values (P at the roots of g_e = X^(2^e)+X+1, in F_{2^(2e)}-extension) are
     counted directly: expected 2^(e-1) (the count does not need gcd(e,m) = 1).
C4c  binary-word lemma used in the proof of Lemma 3.2: odd m in [5,61], all 1 <= k < m (gcd not assumed), e_i = 2^i-2^k-1
     mod 2^m-1: predicted ones-sets / weights, <= 2 zero runs, orbit length m, orbits of e_i (i != 0,k) pairwise distinct
     and distinct from that of e_k, e_0 = 2^k e_k, no orbit is {0}.
Writes controls_R6.json; prints PASS/FAIL lines; exit 0 iff every expectation holds."""
import sys; sys.dont_write_bytecode = True
import json
from math import gcd

RES = {}; FAIL = []
def check(name, cond, msg):
    print(('PASS ' if cond else 'FAIL ') + name + ' ' + msg)
    if not cond: FAIL.append(name)

def mk(m, f):
    q = 1 << m
    def mul(a, b):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a & q: a ^= f
        return r
    return q, mul

def pw(mul, a, e):
    r = 1
    while e:
        if e & 1: r = mul(r, a)
        a = mul(a, a); e >>= 1
    return r

def table(m, f, terms):          # F_2 coefficients
    q, mul = mk(m, f)
    return [__import__('functools').reduce(lambda s, e: s ^ pw(mul, x, e), terms, 0) for x in range(q)]

def du(T):
    q = len(T); best = 0
    for a in range(1, q):
        cnt = {}
        for x in range(q):
            v = T[x ^ a] ^ T[x]; cnt[v] = cnt.get(v, 0) + 1
        best = max(best, max(cnt.values()))
    return best

# ---- C4a
P53 = [1, 2, 3, 9, 10, 18, 24]
def family(m, r):
    V = [1 << i for i in range(r - 2)]; W = 1 << (r - 2); Y = 1 << (m - 2); Z = 1 << (m - 1)
    return sorted(V + [W] + [W + v for v in V] + [W + Y, W + Z] + [Y + v for v in V] + [Y + Z])
check('C4a', family(5, 3) == sorted(P53), 'P_{5,3} exponents from Theorem 3.1(1): %s' % family(5, 3))
T = table(7, 0b10000011, P53)
coll = {}
for x, v in enumerate(T): coll.setdefault(v, []).append(x)
pairs = [xs for xs in coll.values() if len(xs) > 1]
RES['C4a'] = {'P53_on_F128_image_size': len(coll), 'first_collision': pairs[0] if pairs else None,
              'collision_value': T[pairs[0][0]] if pairs else None}
check('C4a', len(coll) < 128, 'fixed P_{5,3} on F_128 (x^7+x+1): image size %d < 128, e.g. %s -> %s' % (len(coll), pairs[0], T[pairs[0][0]]))
RES['C4a']['codes_6_15'] = [T[6], T[15]]
check('C4a', T[6] == T[15] == 100, 'reviewer pair: codes 6 and 15 both map to 100')
for r in (3, 5):
    Tm = table(7, 0b10000011, family(7, r))
    RES['C4a']['P7%d_perm' % r] = len(set(Tm)) == 128
    check('C4a', len(set(Tm)) == 128, 'family member P_{7,%d} permutes F_128' % r)

# ---- C4b
m, f = 9, 0b1000010001
q, mul = mk(m, f)
def tr(a):
    s, x = 0, a
    for _ in range(m): s ^= x; x = mul(x, x)
    return s
t = 2
check('C4b', tr(t) == 0, 'Tr(x) = 0 in F_512 (x^9+x^4+1)')
RES['C4b'] = {}
for e in (1, 2, 3, 4):
    tc = [t]
    for i in range(1, m): tc.append(mul(tc[-1], tc[-1]))          # t^(2^i)
    def P(x):
        Tt = 0; xi = x
        for i in range(m): Tt ^= mul(tc[i], xi); xi = mul(xi, xi)
        A = pw(mul, x, 1 << (e + 1)) ^ mul(x, x) ^ 1
        return pw(mul, x, (1 << (e + 1)) + 2) ^ mul(A, Tt)
    T = [P(x) for x in range(q)]
    der = [mul(t, pw(mul, x, 1 << (e + 1)) ^ mul(x, x) ^ 1) for x in range(q)]
    fib = {}
    for v in der: fib[v] = fib.get(v, 0) + 1
    # branch values: roots of g_e lie in F_{2^(2e)}; P(alpha) = (alpha^2+alpha)^2 (proof of Rem 4.2) -- count them in
    # F_{2^(2e)} built from a primitive polynomial, independent of m.
    E2 = 2 * e; f2 = {2: 0b111, 4: 0b10011, 6: 0b1000011, 8: 0b100011101}[E2]
    q2, mul2 = mk(E2, f2)
    roots = [a for a in range(q2) if pw(mul2, a, 1 << e) ^ a ^ 1 == 0]
    bv = {mul2(mul2(a, a) ^ a, mul2(a, a) ^ a) for a in roots}
    rec = {'gcd': gcd(e, m), 'perm': len(set(T)) == q, 'DU': du(T), 'derivative_zeros': fib.get(0, 0),
           'fibre_sizes': sorted(set(fib.values())), 'n_roots_g_e': len(roots), 'n_branch_values': len(bv)}
    RES['C4b']['e=%d' % e] = rec
    if gcd(e, m) == 1:
        exp = rec['perm'] and rec['DU'] == 2 and rec['derivative_zeros'] == 0 and rec['fibre_sizes'] == [2]
    else:
        exp = rec['perm'] and rec['DU'] == 8 and rec['derivative_zeros'] == 0 and rec['fibre_sizes'] == [8]
    check('C4b', exp, 'e=%d gcd(e,9)=%d: %s' % (e, gcd(e, m), rec))
    check('C4b', len(roots) == 1 << e and len(bv) == 1 << (e - 1), 'e=%d: %d roots of g_e, %d finite branch values (= 2^(e-1))' % (e, len(roots), len(bv)))

# ---- C4c
def words(m, k):
    Q = (1 << m) - 1
    return [((1 << i) - (1 << k) - 1) % Q for i in range(m)], Q
def zero_runs(w, m):
    bits = [(w >> j) & 1 for j in range(m)]
    return sum(1 for j in range(m) if bits[j] == 0 and bits[j - 1] == 1)
n_pairs = 0; ok = True
for m in range(5, 62, 2):
    for k in range(1, m):
        E, Q = words(m, k); n_pairs += 1
        for i in range(m):
            w = E[i]
            if i == 0 or i == k: ones = set(range(m)) - {k if i == 0 else 0}
            elif i < k: ones = set(range(1, i)) | set(range(k, m))
            else: ones = set(range(0, k)) | set(range(k + 1, i))
            if w != sum(1 << j for j in ones) or not (1 <= zero_runs(w, m) <= 2): ok = False
        orb = []
        for i in range(m):
            o = set(); x = E[i]
            for _ in range(m): o.add(x); x = (2 * x) % Q
            orb.append(frozenset(o))
            if len(o) != m or 0 in o: ok = False
        if orb[0] != orb[k] or E[0] != ((1 << k) * E[k]) % Q: ok = False
        others = [orb[i] for i in range(m) if i not in (0, k)]
        if len(set(others)) != m - 2 or orb[k] in set(others): ok = False
RES['C4c'] = {'pairs_checked': n_pairs, 'ok': ok}
check('C4c', ok and n_pairs == sum(m - 1 for m in range(5, 62, 2)), 'binary-word lemma: %d pairs (m,k), odd 5<=m<=61, all 1<=k<m' % n_pairs)

RES['fails'] = FAIL
json.dump(RES, open('controls_R6.json', 'w'), indent=1, sort_keys=True)
sys.exit(1 if FAIL else 0)
