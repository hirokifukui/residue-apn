# Row predictor: R05b Theorems A-C (predict.py) for all pair types they cover, plus the closed forms of
# Theorems I-III (closed.py) for the three formerly open sub-cases.  Returns (row Counter, status, logs).
from collections import Counter
from gr import Ctx, Ring, res, nz
from closed import Node, DD, offset, theorem2_pair, theorem3_class, fill, shift, Fallback, node_kind
import predict as P
def theory_row(ctx):
    C = ctx; q = C.q; R = C.R
    tot, un, info = P.predict(C.terms, C.m, C.k, C.alpha)
    tot = Counter({int(v): c for v, c in tot.items()})
    logs = []; status = 'closed'; kinds = []
    for item in un:
        kind = item[0]; x = item[1]
        a = x; xa = C.center(a)
        try:
            if kind == 'deep2':
                A = Node(C, xa, R.zero, 1, 2); lg = []
                M = theorem3_class(A, lg); kinds.append('III-split'); logs.append(lg)
            elif kind == 'deep2-merged':
                A = Node(C, xa, R.zero, 1, 2); lg = []
                M = shift(theorem3_class(A, lg), 1); kinds.append('III-merged-ND'); logs.append(lg)
            elif kind == 'merged':
                ta, tb = item[2], item[3]
                xb = R.add(xa, C.tau)
                A = Node(C, xa, R.zero, 1, 2); B = Node(C, xb, R.zero, 1, 2); lg = []
                if ta == 'DEG' and tb == 'DEG':
                    M = DD(A, B, offset(A, B), lg); kinds.append('I')
                elif ta == 'DEEP' and tb == 'DEEP':
                    M = theorem2_pair(A, B, lg); kinds.append('II')
                else: raise Fallback(('merged', ta, tb))
                logs.append(lg)
            else: raise Fallback(item)
        except Fallback as ex:
            status = 'fallback'; logs.append(('FALLBACK', str(ex))); continue
        for N, c in M.items():
            if N: tot[N * q ** (C.j + 1)] += c
    if info['checks']: status += '+CHECKFAIL'
    return tot, status, kinds, logs, info
