# Verification runner.  For a lift + row alpha:
#  * closed-form row prediction (R05b Thms A-C + Theorems I-III) and GR-recursion row prediction;
#  * exhaustive brute force: the full row (n<=6, every pair enumerated) or, for n=7, every pair/class of open type;
#  * per open-type pair: closed vs brute, GR vs brute.
import sys, json, time
from collections import Counter
from gr import *
from closed import Node, DD, offset, theorem2_pair, theorem3_class, shift, Fallback
from theory import theory_row
from brute import brute_union2 as brute_union, brute_row_pairs, brute_row
import predict as P
def open_targets(C):
    tot, un, info = P.predict(C.terms, C.m, C.k, C.alpha)
    out = []
    for item in un:
        kind, a = item[0], item[1]; xa = C.center(a); xb = C.R.add(xa, C.tau)
        if kind == 'deep2': out.append(('III-split', a, [xa]))
        elif kind == 'deep2-merged':
            b = a ^ C.rho; out.append(('III-merged-ND', a, [xa, xb]))   # (a is the DEEP class; partner ND, c3=0)
        elif kind == 'merged': out.append(('I' if item[2] == 'DEG' else 'II', a, [xa, xb]))
    return out
def closed_target(C, kind, a, centers, log):
    R = C.R; A = Node(C, centers[0], R.zero, 1, 2)
    if kind == 'III-split': return theorem3_class(A, log)
    if kind == 'III-merged-ND': return shift(theorem3_class(A, log), 1)
    B = Node(C, centers[1], R.zero, 1, 2)
    if kind == 'I': return DD(A, B, offset(A, B), log)
    return theorem2_pair(A, B, log)
def run(termfile, k, alpha_packed, label, out, full=None):
    m = 5; T = read_terms(termfile, m); R = Ring(m, k); alpha = R.unpack(alpha_packed)
    C = Ctx(T, m, k, alpha)
    rec = dict(label=label, file=termfile, k=k, j=C.j, d=C.d, ubar=C.ubar, alpha=alpha_packed)
    t0 = time.time()
    trow, st, kinds, logs, info = theory_row(C)
    grow, per, calls = gr_row(C)
    rec.update(closed_status=st, kinds=kinds, logs=[str(l) for l in logs], closed_row=dict(trow), gr_row=dict(grow),
               closed_eq_gr=(dict(trow) == dict(grow)) if st == 'closed' else None, checks=info['checks'])
    targets = []
    for kind, a, centers in open_targets(C):
        lg = []
        try: Mc = nz(closed_target(C, kind, a, centers, lg)); fb = None
        except Fallback as ex: Mc = None; fb = str(ex)
        g = GR(C); Mg = nz(g.config(C.Tc(centers[0], R.zero), 2, [(x, R.zero, 1, 1) for x in centers]))
        targets.append(dict(kind=kind, a=a, log=[str(x) for x in lg], fallback=fb, closed=dict(Mc) if Mc else None, gr=dict(Mg)))
    if full is None: full = (C.n <= 6)
    if full:
        bf = brute_row_pairs(C); rec['brute_row'] = dict(bf)
        rec['row_closed'] = 'MATCH' if (st == 'closed' and dict(trow) == dict(bf)) else ('FALLBACK' if st != 'closed' else 'MISMATCH')
        rec['row_gr'] = 'MATCH' if dict(grow) == dict(bf) else 'MISMATCH'
    for tg in targets:
        centers = [C.center(tg['a'])] + ([C.R.add(C.center(tg['a']), C.tau)] if tg['kind'] != 'III-split' else [])
        bu = brute_union(C, centers, C.Tc(centers[0], R.zero), sh=2 if tg['kind'] != 'III-merged-ND' else 1)
        tg['brute'] = dict(bu)
        tg['closed_vs_brute'] = 'FALLBACK' if tg['closed'] is None else ('MATCH' if tg['closed'] == dict(bu) else 'MISMATCH')
        tg['gr_vs_brute'] = 'MATCH' if tg['gr'] == dict(bu) else 'MISMATCH'
    rec['targets'] = targets; rec['seconds'] = round(time.time() - t0, 1)
    with open(out, 'a') as fo: fo.write(json.dumps(rec, default=str) + "\n")
    print(label, 'k', k, 'j', C.j, 'd', C.d, st, kinds, rec.get('row_closed'), rec.get('row_gr'),
          [(t['kind'], t['closed_vs_brute'], t['gr_vs_brute']) for t in targets], rec['seconds'], flush=True)
    return rec
if __name__ == '__main__':
    run(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5])
