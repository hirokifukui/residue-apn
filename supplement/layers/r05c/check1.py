# Structural checks for Theorem P / I on the sub-case-1 lifts:
#  (a) nu and c are inherited along the degenerate chain (child phi_2 = parent phi_2 mod 4 for SA nodes);
#  (b) the coincidence count obeys Theorem P(c): with nu' = nu_a/c_a + nu_b/c_b:
#      resonant & nu'!=0 => s=1;  resonant & nu'=0 => s in {0,q};  non-resonant & nu'=0 => s=1;  non-res & nu'!=0 => s in {0,2}.
import json, glob
from gr import *
from closed import Node, offset, deg_data, fit, witt2, DD, Fallback
q = 32; ok = 0; bad = []
def nu_of(node):
    C = node.C; F = C.Fd; c, sig, lam = deg_data(node); co = fit(F, sig); return c, co.get(2, 0), lam
def walk(A, B, e, lvl, out):
    C = A.C; F = C.Fd
    if A.D < 2: return
    ca, nua, la = nu_of(A); cb, nub, lb = nu_of(B)
    log = []; DD(A, B, e, log, 0)
    top = [x for x in log if x[0] == 0 and x[1] in ('res', 'nonres', 'D=2')][0]
    nup = F.mul(nua, F.inv(ca)) ^ F.mul(nub, F.inv(cb))
    s = top[3] if top[1] != 'D=2' else top[2]
    eb = witt2(C, e)[0]
    dp = F.mul(la, F.inv(F.sqrt(ca))) ^ F.mul(lb, F.inv(F.sqrt(cb))) ^ F.sqrt(eb)
    res_ = (dp == 0)
    if top[1] != 'D=2': assert res_ == (top[1] == 'res')
    allowed = ({1} if nup else {0, q}) if res_ else ({0, 2} if nup else {1})
    out.append((lvl, ca, cb, nua, nub, s, res_, s in allowed))
    # descend along the resonant chain with i=1
    if top[1] == 'res' and top[5] == 1:
        tstar = F.mul(F.mul(la, la), F.inv(ca))
        ya = F.sqrt(F.mul(tstar, F.inv(ca))); yb = F.sqrt(F.mul(tstar ^ eb, F.inv(cb)))
        a1, b1 = A.child(ya), B.child(yb); walk(a1, b1, offset(a1, b1), lvl + 1, out)
for l in open('gen1u.jsonl'):
    r = json.loads(l); T = read_terms(r['file'], 5); R = Ring(5, r['k']); C = Ctx(T, 5, r['k'], R.unpack(r['alpha']))
    xa = C.center(r['a']); xb = R.add(xa, C.tau); A = Node(C, xa, R.zero, 1, 2); B = Node(C, xb, R.zero, 1, 2)
    out = []; walk(A, B, offset(A, B), 0, out)
    inh = all(o[1] == out[0][1] and o[2] == out[0][2] and o[3] == out[0][3] and o[4] == out[0][4] for o in out)
    good = inh and all(o[7] for o in out)
    ok += good
    if not good: bad.append((r['file'], out))
print('Theorem P(c) / inheritance checks: OK', ok, 'FAILED', len(bad)); [print(b) for b in bad]
