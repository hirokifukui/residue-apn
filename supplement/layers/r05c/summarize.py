# Summarize verification records (ver*.jsonl) into the table of RESULT_R06.md section 7.
import json, sys, glob
from collections import Counter, defaultdict
files = sys.argv[1:] or sorted(glob.glob('ver*.jsonl'))
byk = {}
for fn in files:
    for l in open(fn):
        r = json.loads(l); key = (r['file'], r['k'], r['alpha'])
        if key in byk and ('row_closed' not in r or 'row_closed' in byk[key]): continue
        byk[key] = r          # keep the record that has a full brute-force row, if any
recs = list(byk.values())
def sub(kind): return {'I': '1', 'II': '2', 'III-split': '3', 'III-merged-ND': '3'}[kind]
T = defaultdict(Counter)
for r in recs:
    kinds = {sub(t['kind']) for t in r['targets']}
    for t in r['targets']:
        s = sub(t['kind'])
        T[(s, r['d'])]['targets'] += 1
        T[(s, r['d'])]['closed_' + t['closed_vs_brute']] += 1
        T[(s, r['d'])]['gr_' + t['gr_vs_brute']] += 1
    if 'row_closed' in r:
        for s in kinds:
            T[(s, r['d'])]['rows'] += 1
            T[(s, r['d'])]['row_closed_' + r['row_closed']] += 1
            T[(s, r['d'])]['row_gr_' + r['row_gr']] += 1
    if r.get('closed_eq_gr') is False:
        for s in kinds: T[(s, r['d'])]['closed!=gr'] += 1
    if r.get('checks'):
        for s in kinds: T[(s, r['d'])]['CHECKFAIL'] += 1
cols = ['targets', 'closed_MATCH', 'closed_MISMATCH', 'closed_FALLBACK', 'gr_MATCH', 'gr_MISMATCH', 'rows',
        'row_closed_MATCH', 'row_closed_MISMATCH', 'row_closed_FALLBACK', 'row_gr_MATCH', 'row_gr_MISMATCH', 'closed!=gr', 'CHECKFAIL']
print('| sub-case | d | ' + ' | '.join(cols) + ' |'); print('|' + '---|' * (len(cols) + 2))
tot = Counter()
for key in sorted(T):
    print(f'| {key[0]} | {key[1]} | ' + ' | '.join(str(T[key][c]) for c in cols) + ' |')
    for c in cols: tot[c] += T[key][c]
print('| all | | ' + ' | '.join(str(tot[c]) for c in cols) + ' |')
print('distinct (lift,row) records:', len(recs))
