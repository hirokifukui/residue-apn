# Closed-form predictors for the three sub-cases (Theorems I, II, III of RESULT_R06.md).
# Every invariant is computed from O(q) values of T per level; the multisets are then assembled from the
# closed formulas of the theorems.  Anything outside the closed formulas raises Fallback (the caller may then use
# the general recursion of Lemma GR, gr.py).
from collections import Counter
from gr import Ctx, res, sub_n, nz
from lifts import interp

class Fallback(Exception): pass

class Node:
    """Phi(z) = (T(c + p + 2^E z) - T(c+p)) / 2^v, a polynomial over R (in all uses below); depth D = n - v."""
    def __init__(s, ctx, c, p, E, v):
        s.C = ctx; s.c = c; s.p = p; s.E = E; s.v = v; s.D = ctx.n - v
        s.V0 = ctx.Tc(c, p); s._val = {}
    def pt(s, y):  # c + p + 2^E [y]  (returned as the offset h from c)
        R = s.C.R
        return R.add(s.p, R.smul(1 << s.E, s.C.teich[y]))
    def val(s, y):
        if y not in s._val:
            s._val[y] = sub_n(s.C.Rn, s.C.Tc(s.c, s.pt(y)), s.V0, s.v)
        return s._val[y]
    def resid(s): return [res(s.val(y)) for y in range(s.C.q)]
    def crit(s, y):
        R = s.C.R; h = s.pt(y)
        a = s.C.Tc(s.c, h); b = s.C.Tc(s.c, R.add(h, R.smul(1 << (s.E + 1), R.one)))
        return all(((x - z) % (1 << (s.v + 2))) == 0 for x, z in zip(a, b))
    def child(s, y): return Node(s.C, s.c, s.pt(y), s.E + 1, s.v + 2)
    def half(s): return Node(s.C, s.c, s.p, s.E, s.v + 1)

def offset(A, B):
    """e with N_A(g) + N_B(g+e) the pair value, i.e. e = (T_A(0) - T_B(0))/2^v."""
    assert A.v == B.v
    return sub_n(A.C.Rn, A.V0, B.V0, A.v)

def fit(F, table):
    """polynomial coefficients (dict exp->coef) of a function F_q -> F_q."""
    return interp(F, table)

def witt2(ctx, x):
    """x (tuple, mod >=4) = [x0] + 2[x1] mod 4; returns (x0,x1)."""
    x0 = res(x); t = tuple(v % 4 for v in ctx.teich[x0])
    d = tuple((a - b) % 4 for a, b in zip(x, t)); assert all(v % 2 == 0 for v in d)
    return x0, res(tuple(v // 2 for v in d))

# ---------- universal multisets (incl. zeros) ----------
def S_nd(q, cnz, D):
    if D == 0: return Counter({1: 1})
    return Counter({2: q ** D // 2, 0: q ** D // 2}) if cnz else Counter({1: q ** D})
_md = {}
def S_deg(q, D):
    if (q, D) in _md: return _md[(q, D)]
    if D == 0: r = Counter({1: 1})
    elif D == 1: r = Counter({1: q})
    else:
        r = Counter()
        for v, c in S_deg(q, D - 2).items(): r[q * v] += c
        for v, c in S_nd(q, True, D - 2).items(): r[q * v] += (q - 1) * c
        r[0] += q ** D - q ** (D - 1)
    _md[(q, D)] = r; return r
def scale(M, f): return Counter({f * v: c for v, c in M.items()})
def shift(M, a): return Counter({v + a: c for v, c in M.items()})
def add(*Ms):
    r = Counter()
    for M in Ms:
        for v, c in M.items(): r[v] += c
    return r
def fill(M, total):
    M = nz(M); s = sum(M.values()); assert s <= total, (s, total); M[0] += total - s; return M

# ---------- type of an additive-residue node ----------
FAST = False   # generators only: fit additive polynomials from a few points (checked at two more points)
def solve_add(F, f):
    """coefficients (l1,l2,l4) of f(y)=l1 y+l2 y^2+l4 y^4 from f at y=1,2,4 (Gaussian elimination over F_q)."""
    ys = [1, 2, 4]
    A = [[y, F.mul(y, y), F.pow(y, 4), f(y)] for y in ys]
    for c in range(3):
        p = next(r for r in range(c, 3) if A[r][c])
        A[c], A[p] = A[p], A[c]
        iv = F.inv(A[c][c]); A[c] = [F.mul(iv, v) for v in A[c]]
        for r in range(3):
            if r != c and A[r][c]:
                fac = A[r][c]; A[r] = [v ^ F.mul(fac, w) for v, w in zip(A[r], A[c])]
    co = {e: A[i][3] for i, e in enumerate((1, 2, 4)) if A[i][3]}
    for y in (3, 7):
        if _ev(F, co, y) != f(y): raise Fallback(('fast fit failed', co))
    return co
def shape(node):
    """residue of a node as additive polynomial: returns dict {1:w,2:c,4:..} (asserts additivity)."""
    F = node.C.Fd
    if FAST: return solve_add(F, lambda y: res(node.val(y)))
    co = fit(F, node.resid())
    for e in co:
        if e not in (1, 2, 4, 8, 16): raise Fallback(('non-additive residue', co))
    return co

def n_fun(F, w, c):
    """n(g) = #{y : w y + c y^2 = g} as a table."""
    t = [0] * F.q
    for y in range(F.q): t[F.mul(w, y) ^ F.mul(c, F.mul(y, y))] += 1
    return t

# ---------- Lemma T2: a DEG node (residue c y^2) plus a residue-level background H ----------
def deg_plus_background(q, D, H, gstar):
    """N(g) = N_deg(g) + H(gbar): the DEG node has its unique degenerate grandchild over residue gstar (D>=3).
       Returns multiset incl. zeros over q^D targets."""
    if D == 0: raise ValueError
    out = Counter()
    if D == 1:
        for g in range(q): out[H[g] + 1] += 1
        return out
    for g in range(q):
        out[H[g]] += q ** (D - 1) - q ** (D - 2)
        child = S_deg(q, D - 2) if (D >= 3 and g == gstar) else S_nd(q, True, D - 2)
        for v, c in child.items(): out[q * v + H[g]] += c
    return out

def deg_data(node):
    """For a DEG node (w=0, c!=0): c, sigma table (2nd Witt digit of Phi([y]) mod 4), lambda (linear coeff of sigma)."""
    C = node.C; F = C.Fd; q = C.q
    co = shape(node)
    if co.get(1, 0) or not co.get(2, 0) or any(e > 2 for e in co): raise Fallback(('not DEG', co))
    c = co[2]
    if FAST:
        sc = solve_add(F, lambda y: witt2(C, node.val(y))[1]); return c, None, sc.get(1, 0)
    sig = []
    for y in range(q):
        x0, x1 = witt2(C, node.val(y)); assert x0 == F.mul(c, F.mul(y, y)); sig.append(x1)
    sc = fit(F, sig)
    for e in sc:
        if e not in (1, 2, 4, 8, 16): raise Fallback(('sigma not additive', sc))
    return c, sig, sc.get(1, 0)

def gstar_of(node):
    """residue over which the DEG node's child is degenerate: lambda^2/c (Prop. 5(b))."""
    F = node.C.Fd; c, sig, lam = deg_data(node)
    return F.mul(F.mul(lam, lam), F.inv(c))

# ---------- Theorem 1: merged pair of two DEG nodes ----------
def DD(A, B, e, log, lvl=0):
    """Multiset (incl. zeros, q^D targets) of N_A(g)+N_B(g+e), A,B DEG nodes (admissible, additive sigma)."""
    C = A.C; F = C.Fd; q = C.q; D = A.D; Rn = C.Rn
    if D == 0: return Counter({2: 1})
    if D == 1: log.append((lvl, 'D=1')); return Counter({2: q})
    ca, siga, lama = deg_data(A); cb, sigb, lamb = deg_data(B)
    eb, e1 = witt2(C, e)
    # coincidence over target residues gbar
    roots = []
    for g in range(q):
        ya = F.sqrt(F.mul(g, F.inv(ca))); yb = F.sqrt(F.mul(g ^ eb, F.inv(cb)))
        Va = A.val(ya); Vb = B.val(yb)
        co = all(((x + ee - z) % 4) == 0 for x, ee, z in zip(Va, e, Vb))
        roots.append((ya, yb, co))
    s = sum(1 for r in roots if r[2])
    if D == 2:
        log.append((lvl, 'D=2', s))
        return fill(Counter({2 * q: s, q: 2 * (q - s)}), q * q)
    Dp = D - 2
    # children
    Wa, Wb, kids = [], [], []
    for g, (ya, yb, co) in enumerate(roots):
        a1 = A.child(ya); b1 = B.child(yb)
        sa = shape(a1); sb = shape(b1)
        if sa.get(2, 0) != ca or sb.get(2, 0) != cb or any(x > 2 for x in list(sa) + list(sb)): raise Fallback('child shape')
        Wa.append(sa.get(1, 0)); Wb.append(sb.get(1, 0)); kids.append((a1, b1))
        # Prop 5(b): W_a = lam_a + c_a y_a
        assert Wa[-1] == lama ^ F.mul(ca, ya) and Wb[-1] == lamb ^ F.mul(cb, yb)
    ga = [g for g in range(q) if Wa[g] == 0]; gb = [g for g in range(q) if Wb[g] == 0]
    assert len(ga) == 1 and len(gb) == 1
    ga, gb = ga[0], gb[0]
    resonant = (ga == gb)
    nd4 = Counter({4: q ** Dp // 4, 2: q ** Dp // 2, 0: q ** Dp // 4})
    two = Counter({2: q ** Dp})
    def eprime(g):
        ya, yb, _ = roots[g]
        return sub_n(Rn, tuple((x + ee) % (1 << D) for x, ee in zip(A.val(ya), e)), B.val(yb), 2)
    def same_hyper(g):  # W_a^2/c_a == W_b^2/c_b
        return F.mul(F.mul(Wa[g], Wa[g]), F.inv(ca)) == F.mul(F.mul(Wb[g], Wb[g]), F.inv(cb))
    if not resonant:
        sp = sum(1 for g in range(q) if roots[g][2] and g not in (ga, gb))
        for g in range(q):
            if roots[g][2] and g not in (ga, gb): assert not same_hyper(g)
        X = []
        for side, gs in (('a', ga), ('b', gb)):
            if roots[gs][2]:
                a1, b1 = kids[gs]; ep = eprime(gs); epb = res(ep)
                if side == 'a':   # DEG child a, ND child b (w=Wb, c=cb): background H(g') = n_b(g'+e')
                    nb = n_fun(F, Wb[gs], cb); H = [nb[g ^ epb] for g in range(q)]
                    gst = gstar_of(a1) if Dp >= 3 else None
                else:             # DEG child b; reindex by g''=g'+e': background n_a(g''+e')
                    na = n_fun(F, Wa[gs], ca); H = [na[g ^ epb] for g in range(q)]
                    gst = gstar_of(b1) if Dp >= 3 else None
                kap = (H[gst] // 2) if gst is not None else None
                X.append(deg_plus_background(q, Dp, H, gst)); log.append((lvl, 'DN', side, kap))
            else:
                X.append(add(S_deg(q, Dp), S_nd(q, True, Dp)))
        M = add(scale(add(*([nd4] * sp)), q), scale(add(*([two] * (q - 2 - sp))), q), scale(X[0], q), scale(X[1], q))
        log.append((lvl, 'nonres', D, s, sp, int(roots[ga][2]), int(roots[gb][2])))
        return fill(M, q ** D)
    # resonant
    r = 0; nC = 0
    for g in range(q):
        if roots[g][2] and g != ga:
            assert same_hyper(g); nC += 1
            ep = res(eprime(g))
            chi = F.tr(F.mul(F.mul(ca, ep), F.inv(F.mul(Wa[g], Wa[g]))))
            if chi == 0: r += 1
    i = int(roots[ga][2])
    if i:
        a1, b1 = kids[ga]
        X = DD(a1, b1, eprime(ga), log, lvl + 1)
    else:
        X = add(S_deg(q, Dp), S_deg(q, Dp))
    M = add(scale(add(*([Counter({4: q ** Dp // 2, 0: q ** Dp // 2})] * r)), q),
            scale(add(*([two] * (q - 1 - r))), q), scale(X, q))
    log.append((lvl, 'res', D, s, r, i))
    return fill(M, q ** D)

# ---------- residue-level (Hensel) configurations, Lemma T1 ----------
def hensel_pair(q, D, na, nb, eb):
    """N_a(g)+N_b(g+e) for two Hensel nodes with residue fibre-count tables na, nb (eb = residue of e)."""
    out = Counter()
    for g in range(q): out[na[g] + nb[g ^ eb]] += q ** (D - 1)
    return out

def additive_table(F, co):
    return [0 if False else _ev(F, co, y) for y in range(F.q)]
def _ev(F, co, y):
    r = 0
    for e, c in co.items(): r ^= F.mul(c, F.pow(y, e))
    return r
def fibre_counts(F, fun):
    t = [0] * F.q
    for y in range(F.q): t[fun[y]] += 1
    return t

def node_kind(node):
    """ND / DEG / DEEP (residue identically 0) for a node whose residue is w y + c y^2 (asserted)."""
    co = shape(node)
    if any(e > 2 for e in co): raise Fallback(('residue not of form wy+cy^2', co))
    w, c = co.get(1, 0), co.get(2, 0)
    return ('ND' if w else ('DEG' if c else 'DEEP')), w, c

# ---------- Theorem III: DEEP class with w'=c'=0 (quarter node Psi = Phi/4) ----------
def quarter_multiset(Psi, log):
    """Multiset (incl. zeros, q^D targets, D = depth of Psi) of N_Psi."""
    C = Psi.C; F = C.Fd; q = C.q; D = Psi.D
    if D == 0: return Counter({1: 1})
    co = shape(Psi)
    if any(e not in (1, 2, 4) for e in co): raise Fallback(('L not of degree<=4', co))
    L = additive_table(F, co); nL = fibre_counts(F, L)
    lam1 = co.get(1, 0); lam2 = co.get(2, 0); c5 = co.get(4, 0)
    log.append(('III', D, lam1, lam2, c5, max(nL)))
    if D == 1 or lam1:
        out = Counter()
        for g in range(q): out[nL[g]] += q ** (D - 1)
        return out
    if not any(co.values()): raise Fallback('L == 0 (Theorem III(e))')
    # lam1 = 0: every point critical; children residue mu(y) z + lam2 z^2; fibres of L have size <= 2
    out = Counter(); used = Counter()
    for g in range(q):
        Y = [y for y in range(q) if L[y] == g]
        groups = {}
        for y in Y:
            assert Psi.crit(y)
            key = tuple(x % 4 for x in Psi.val(y))
            groups.setdefault(key, []).append(y)
        for key, ys in groups.items():
            kids = [Psi.child(y) for y in ys]
            M = config_multiset(kids, log)
            for v, c in M.items(): out[q * v] += c
            used[g] += 1
    for g in range(q): out[0] += q ** (D - 1) - used[g] * q ** (D - 2)
    return out

def config_multiset(kids, log):
    """Closed-form multiset for a configuration of 1 or 2 nodes in a common frame (Lemmas T1, T2, Theorem I)."""
    C = kids[0].C; F = C.Fd; q = C.q; D = kids[0].D
    if D == 0: return Counter({len(kids): 1})
    if len(kids) == 1:
        kd, w, c = node_kind(kids[0])
        if kd == 'ND': return S_nd(q, c != 0, D)
        if kd == 'DEG': return S_deg(q, D)
        # zero residue (Lemma Z): N(g) = q [g in 2R] N_{Phi/2}(g/2); closed when Phi/2 is Hensel (Lemma T1)
        X = kids[0]
        if D == 1: return Counter({q: 1, 0: q - 1})
        h = X.half()
        if h.D <= 1 or all(not h.crit(y) for y in range(q)):
            nh = fibre_counts(F, h.resid()); out = Counter()
            for t in range(q): out[q * nh[t]] += q ** (D - 2)
            out[0] += q ** D - q ** (D - 1)
            log.append(('Z-hensel', D))
            return out
        raise Fallback('zero-residue node with non-Hensel half')
    if len(kids) != 2: raise Fallback('>2 nodes')
    A, B = kids; e = offset(A, B); eb = res(e)
    ka, wa, ca = node_kind(A); kb, wb, cb = node_kind(B)
    if ka == 'ND' and kb == 'ND':
        return hensel_pair(q, D, n_fun(F, wa, ca), n_fun(F, wb, cb), eb)
    if {ka, kb} == {'ND', 'DEG'}:
        if ka == 'DEG':
            nb = n_fun(F, wb, cb); H = [nb[g ^ eb] for g in range(q)]; dn = A
        else:
            na = n_fun(F, wa, ca); H = [na[g ^ eb] for g in range(q)]; dn = B
        gst = gstar_of(dn) if D >= 3 else None
        log.append(('T2', D, None if gst is None else H[gst]))
        return deg_plus_background(q, D, H, gst)
    if ka == 'DEG' and kb == 'DEG':
        return DD(A, B, e, log, 1)
    raise Fallback(('config', ka, kb))

def theorem3_class(A, log):
    """Class multiset (incl. zeros, q^d) of a DEEP class with w'=c'=0:  N = q^2 [g in 4R] N_Psi(g/4)."""
    C = A.C; q = C.q; d = A.D
    h = A.half(); kd, w, c = node_kind(h); assert kd == 'DEEP'
    if d == 1: return Counter({q: 1, 0: q - 1})
    Psi = h.half()
    M = quarter_multiset(Psi, log)
    return fill(scale(M, q * q), q ** d)

def deep_class(A, log):
    """Theorem B(4) + Theorem III: class multiset (incl. zeros) of a DEEP class node A (depth d)."""
    C = A.C; q = C.q; d = A.D
    if d == 1: return Counter({q: 1, 0: q - 1})
    h = A.half(); kd, w, c = node_kind(h)
    if kd == 'ND': base = S_nd(q, c != 0, d - 1)
    elif kd == 'DEG': base = S_deg(q, d - 1)
    else: return theorem3_class(A, log)
    return fill(scale(base, q), q ** d)

# ---------- Theorem II: merged DEEP+DEEP pair ----------
def theorem2_pair(A, B, log):
    C = A.C; F = C.Fd; q = C.q; d = A.D
    e = offset(A, B); eb = res(e)
    if d == 1:
        return Counter({2 * q: 1, 0: q - 1}) if eb == 0 else Counter({q: 2, 0: q - 2})
    if eb:
        log.append(('II', 'split'))
        return fill(add(deep_class(A, log), deep_class(B, log)), q ** d)
    hA, hB = A.half(), B.half(); D = d - 1
    eps = tuple(v // 2 for v in e)        # e/2 (e in 2R), mod 2^(d-1)
    ka, wa, ca = node_kind(hA); kb, wb, cb = node_kind(hB)
    log.append(('II', 'merged', ka, kb))
    epsb = res(eps)
    if ka != 'DEEP' and kb != 'DEEP':
        M = config_multiset([hA, hB], log)
    else:
        M = deep2_halfpair(hA, hB, ka, kb, eps, log)
    return fill(scale(M, q), q ** d)

def deep2_halfpair(hA, hB, ka, kb, eps, log):
    C = hA.C; F = C.Fd; q = C.q; D = hA.D; epsb = res(eps)
    if ka == 'DEEP' and kb == 'DEEP':
        Pa, Pb = hA.half(), hB.half()
        if epsb:
            return fill(add(scale(quarter_multiset(Pa, log), q), scale(quarter_multiset(Pb, log), q)), q ** D)
        if D == 1: return Counter({2 * q: 1, 0: q - 1})
        coa, cob = shape(Pa), shape(Pb)
        if D - 1 == 1 or (coa.get(1, 0) and cob.get(1, 0)):
            na = fibre_counts(F, additive_table(F, coa)); nb = fibre_counts(F, additive_table(F, cob))
            eps2 = tuple(v // 2 for v in eps)
            log.append(('II', 'quarter-pair-hensel'))
            return fill(scale(hensel_pair(q, D - 1, na, nb, res(eps2)), q), q ** D)
        raise Fallback('quarter pair, non-Hensel')
    # exactly one DEEP2 half; orient so that the DEEP2 half is X and the other is Y, background in X's frame
    if ka == 'DEEP': X, Y, wy_, kind = hA, hB, None, kb
    else: X, Y, kind = hB, hA, ka
    _, wY, cY = node_kind(Y)
    Psi = X.half()
    if D == 1:   # residue level: DEEP2 half gives q[t=0]; ND half n(t); DEG half 1
        nY = n_fun(F, wY, cY) if kind == 'ND' else [1] * q
        out = Counter()
        for t in range(q): out[q * (t == 0) + nY[t ^ epsb]] += 1
        log.append(('II', 'DEEP2+' + kind, 'D=1')); return out
    if kind == 'ND':
        nY = n_fun(F, wY, cY); H = [nY[g ^ epsb] for g in range(q)]
        MP = quarter_multiset(Psi, log)
        out = Counter()
        for g in range(q):
            if g: out[H[g]] += q ** (D - 1)
        for v, c in MP.items(): out[q * v + H[0]] += c
        log.append(('II', 'DEEP2+ND'))
        return out
    # DEEP2 + DEG: closed when Psi is Hensel (lambda1 != 0) or D-1 == 1
    co = shape(Psi)
    if not (co.get(1, 0) or D - 1 == 1): raise Fallback('DEEP2(non-Hensel)+DEG')
    if D < 2: raise Fallback('D<2')
    nL = fibre_counts(F, additive_table(F, co))
    # frame of X: targets g; Y is hit at g+eps' where eps' = offset(X,Y)
    ep = offset(X, Y); epb = res(ep)
    cY_, sig, lam = deg_data(Y)
    out = Counter()
    gsY = gstar_of(Y) if D >= 3 else None   # in Y's own frame
    for g in range(q):
        gy = g ^ epb                          # residue of the target in Y's frame
        child = S_deg(q, D - 2) if (D >= 3 and gy == gsY) else S_nd(q, True, D - 2)
        if g:
            out[0] += q ** (D - 1) - q ** (D - 2)
            for v, c in child.items(): out[q * v] += c
        else:
            # targets g = 2g'; X contributes q*nL(res g'); Y hits one coset of 4R: g' residue t0
            y0 = F.sqrt(F.mul(gy, F.inv(cY)))
            VY = Y.val(y0)                    # Phi_Y([y0]) ; target g with g+ep = VY mod 4
            tt = tuple((a - b) % 4 for a, b in zip(VY, ep))
            assert res(tt) == 0
            t0 = res(tuple(x // 2 for x in tt))
            for gp in range(q):
                if gp != t0: out[q * nL[gp]] += q ** (D - 2)
            for v, c in child.items(): out[q * nL[t0] + q * v] += c
    log.append(('II', 'DEEP2+DEG'))
    return out
