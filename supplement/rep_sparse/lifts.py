# Lifts of p_c: natural (0/1 digits) and the certified lift F_flat.
#   F_flat = F_nat + 2[(c+1) rho^-7] X^13 + 2[rho^-7] X^(9+2^(m-2))   (m>=7)
#   F_flat = F_nat + 2[(c+1) rho^-7] X^13                              (m=5)
#   then, if Tr(A_F(0) + q(rho)) = 0, the X^5 coefficient is increased by 2[rho^-4]  (no new monomial).
import sys, json, subprocess
sys.path.insert(0, '/home/claude/w/research/sparse_r06')
from family import *
D = '/home/claude/w/research/sparse_r06'
POLY = {int(l.split()[0]): int(l.split()[1]) for l in open(D + '/polys.txt')}
def bits(F, x): return [(x >> i) & 1 for i in range(F.m)]
def nat_terms(F, c):
    cd, ld = poly_of(F, c)
    T = {}
    for (u, v), a in cd.items(): T[(1 << u) + (1 << v)] = bits(F, a)
    for u, a in ld.items(): T[1 << u] = bits(F, a)
    return T
def write_terms(T, fn):
    with open(fn, 'w') as f:
        f.write('%d\n' % len(T))
        for e in sorted(T): f.write('%d %s\n' % (e, ' '.join(map(str, T[e]))))
def add2(T, e, F, lam):
    d = T.get(e, [0] * F.m)
    T[e] = [x + 2 * b for x, b in zip(d, bits(F, lam))]
def Kfun(F, c, y):
    m = F.m
    return F.mul(c ^ 1, F.frob(y, 2)) ^ F.mul(F.sq(c), F.frob(y, 3)) ^ F.frob(y, m - 2) if m >= 7 else \
           F.mul(c ^ 1, F.frob(y, 2)) ^ F.mul(1 ^ F.sq(c), F.frob(y, 3))
def qrho(F, c, rho):
    m = F.m; r7 = F.inv(F.pow(rho, 7))
    v = F.mul(F.mul(c ^ 1, r7), F.pow(rho, 12))
    if m >= 7: v ^= F.mul(r7, F.mul(F.pow(rho, 8), F.frob(rho, m - 2)))
    return v
def aset(m, k, fn, rho):
    o = subprocess.run([D + '/gr', 'aset', str(m), str(POLY[m]), str(k), fn, str(rho)], capture_output=True, text=True, check=True)
    return json.loads(o.stdout)
def build(m, c, tag=''):
    F = GF(m, POLY[m]); B = Bco(F, c)
    assert lin_invertible(F, B) and c not in (0, 1)
    rho = solve_lin(F, B, 1)
    Tn = nat_terms(F, c); fn_nat = '%s/terms/m%d_c%d_nat.txt' % (D, m, c); write_terms(Tn, fn_nat)
    An = aset(m, 3, fn_nat, rho)
    # check A_F(a) = A_F(0) + K(sqrt(a rho)) + rho K(a)
    lin_ok = all(An['A'][a] == An['A0'] ^ Kfun(F, c, F.frob(F.mul(a, rho), m - 1)) ^ F.mul(rho, Kfun(F, c, a)) for a in range(F.q))
    Tf = {e: list(d) for e, d in Tn.items()}
    r7 = F.inv(F.pow(rho, 7))
    add2(Tf, 13, F, F.mul(c ^ 1, r7))
    if m >= 7: add2(Tf, 9 + (1 << (m - 2)), F, r7)
    kap = An['A0'] ^ qrho(F, c, rho)
    eps = 1 ^ F.tr(kap)
    if eps: add2(Tf, 5, F, F.inv(F.pow(rho, 4)))
    fn_flat = '%s/terms/m%d_c%d_flat.txt' % (D, m, c); write_terms(Tf, fn_flat)
    Af = aset(m, 3, fn_flat, rho)
    pred_ok = all(Af['A'][a] == kap ^ eps ^ Kfun(F, c, F.frob(F.mul(a, rho), m - 1)) for a in range(F.q))
    return dict(m=m, c=c, rho=rho, nat_terms=len(Tn), flat_terms=len(Tf), A_nat_zeros=An['zeros'], A_nat0=An['A0'],
                Lp_formula_ok=lin_ok, eps=eps, A_flat_zeros=Af['zeros'], A_flat_formula_ok=pred_ok,
                fn_nat=fn_nat, fn_flat=fn_flat)
if __name__ == '__main__':
    m = int(sys.argv[1]); cs = list(map(int, sys.argv[2:]))
    for c in cs: print(json.dumps(build(m, c)), flush=True)
