# Checks the maximum-entry statements against brute force, using only the level data recorded in the logs.
#  Theorem P / I: max from the chain recursion of section 2.4, and m_deg(d) <= max <= 2 m_deg(d).
#  Theorem II: max >= q (ebar != 0) / >= 2q (ebar = 0).   Theorem III: max >= q^2, '= q^2' criterion.
import json, glob, ast, sys
from collections import defaultdict
q = 32
def mdeg(D): return 1 if D <= 1 else (q ** (D // 2) if D % 2 == 0 else 2 * q ** ((D - 1) // 2))
def mT2(D, k): return {1: 3, 2: q + 2, 3: 2 * q + 2}.get(D, q * mdeg(D - 2) + 2 * (k or 0))
def maxDD(log, lvl=0):
    ent = [e for e in log if e[0] == lvl and e[1] in ('res', 'nonres', 'D=2', 'D=1')][0]
    if ent[1] == 'D=1': return 2
    if ent[1] == 'D=2': return 2 * q if ent[2] > 0 else q
    D = ent[2]; Dp = D - 2
    if ent[1] == 'nonres':
        _, _, D, s, sp, ia, ib = ent
        dn = {e[2]: e[3] for e in log if e[0] == lvl and e[1] == 'DN'}
        Xa = mT2(Dp, dn.get('a')) if ia else max(mdeg(Dp), 2)
        Xb = mT2(Dp, dn.get('b')) if ib else max(mdeg(Dp), 2)
        return q * max(2, 4 if sp > 0 else 0, Xa, Xb)
    _, _, D, s, r, i = ent
    X = maxDD(log, lvl + 1) if i else mdeg(Dp)
    return q * max(2, 4 if r > 0 else 0, X)
stat = defaultdict(lambda: [0, 0]); extremes = defaultdict(set)
for fn in sorted(glob.glob('ver*.jsonl')):
    for l in open(fn):
        r = json.loads(l)
        for t in r['targets']:
            bmax = max(int(v) for v in t['brute'])
            d = r['d']
            if t['kind'] == 'I':
                log = [ast.literal_eval(x) for x in t['log']]
                lv = [e for e in log if isinstance(e[0], int)]
                m = maxDD(lv); ok = (m == bmax) and mdeg(d) <= bmax <= 2 * mdeg(d)
                if bmax == mdeg(d): extremes[('I', d)].add('lower')
                if bmax == 2 * mdeg(d): extremes[('I', d)].add('upper')
                stat['I'][0 if ok else 1] += 1
                if not ok: print('I max FAIL', r['file'], m, bmax)
            elif t['kind'] == 'II':
                split = any('split' in x for x in t['log'])
                lb = q if split else 2 * q
                ok = bmax >= lb; stat['II'][0 if ok else 1] += 1
                if bmax == lb: extremes[('II', 'split' if split else 'merged')].add('equality')
                if not ok: print('II max FAIL', r['file'], bmax)
            else:
                ok = bmax >= q * q; stat['III'][0 if ok else 1] += 1
                lg = [ast.literal_eval(x) for x in t['log'] if x.startswith("('III'")]
                if lg:
                    _, D, l1, l2, c5, nLmax = lg[0]
                    crit = (d == 2) or (nLmax == 1 and (d == 3 or l1 != 0))
                    base = 1 if t['kind'] == 'III-split' else 0   # merged with ND adds +1
                    eq = (bmax == q * q + (0 if t['kind'] == 'III-split' else 1))
                    if eq != crit: print('III criterion FAIL', r['file'], bmax, crit); stat['III'][1] += 1
print({k: {'ok': v[0], 'fail': v[1]} for k, v in stat.items()}); print(dict(extremes))
