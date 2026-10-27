# Checks of the structural statements of Theorem III(5) on the sub-case-3 lifts with lambda1 = 0 and depth(Psi) >= 2:
#   every point critical; child residue = mu(y) z + lambda2 z^2 with mu(y) = mu0 + lambda2 y + theta y^2,
#   theta = p^[4](a) + [j=1] ubar c5; sigma_Psi(y) = mu0 y + nu2 y^2 + (theta + sqrt(lambda2 c5)) y^3 + nu4 y^4.
import json
from gr import *
from closed import Node, fit, witt2
from pinv import peval
ok = 0; bad = []; stats = {}
import itertools
for l in itertools.chain(open('gen3.jsonl'), open('gen3b.jsonl')):
    r = json.loads(l)
    if 'info' in r and r['info']['l1'] != 0: continue
    T = read_terms(r['file'], 5); R = Ring(5, r['k']); C = Ctx(T, 5, r['k'], R.unpack(r['alpha'])); F = C.Fd
    Psi = Node(C, C.center(r['a']), R.zero, 1, 4)
    if Psi.D < 2: continue
    co0 = fit(F, Psi.resid()) if Psi.D >= 1 else {}
    if co0.get(1, 0): continue
    l2 = co0.get(2, 0); c5 = C.c5
    theta = peval(F, C.pc, r['a'], 4) ^ (F.mul(C.ubar, c5) if C.j == 1 else 0)
    good = all(Psi.crit(y) for y in range(32))
    mu = []
    for y in (range(32) if Psi.D >= 3 else []):
        ch = Psi.child(y); co = fit(F, ch.resid())
        good &= set(co) <= {1, 2} and co.get(2, 0) == l2
        mu.append(co.get(1, 0))
    mc = fit(F, mu) if mu else None
    if mc is not None: good &= set(mc) <= {0, 1, 2} and mc.get(1, 0) == l2 and mc.get(2, 0) == theta
    sig = [witt2(C, Psi.val(y))[1] for y in range(32)]
    sc = fit(F, sig)
    good &= set(sc) <= {1, 2, 3, 4} and sc.get(3, 0) == theta ^ F.sqrt(F.mul(l2, c5)) and (mc is None or sc.get(1, 0) == mc.get(0, 0))
    if l2 and c5 and Psi.D >= 2:
        eta = F.sqrt(F.mul(l2, F.inv(c5)))
        nco = sum(1 for y in range(32) if all(((u - v) % 4) == 0 for u, v in zip(Psi.val(y), Psi.val(y ^ eta)))) // 2
        resn = F.mul(theta, theta) == F.mul(l2, c5)
        good &= (nco in (0, 16)) if resn else (nco <= 1)
        stats[(resn, nco)] = stats.get((resn, nco), 0) + 1
    if good: ok += 1
    else: bad.append((r['file'], r['k'], mc, sc, theta))
print('Theorem III(5) structure checks: OK', ok, 'FAILED', len(bad)); [print(b) for b in bad]
print('fibre-coincidence stats (resonant, #coincident fibres): count', stats)
