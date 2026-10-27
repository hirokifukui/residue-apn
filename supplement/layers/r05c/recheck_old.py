# Re-grade the 691 R05b rows (brute spectra stored in r07/layers/res_k*.jsonl) with the new row predictor
# (R05b Thms A-C + Theorems I-III) and with the GR recursion.
import json, glob
from collections import Counter
from gr import *
from theory import theory_row
idx = json.load(open('lifts/index.json')); m = 5
st = Counter(); out = open('recheck_old.jsonl', 'w')
for fn in sorted(glob.glob('/home/claude/w/r07/layers/res_k*.jsonl')):
    for l in open(fn):
        r = json.loads(l)
        if r['lift'] not in idx: st['nolift'] += 1; continue
        T = read_terms(idx[r['lift']]['file'], m); k = r['k']; R = Ring(m, k)
        C = Ctx(T, m, k, R.unpack(r['alpha']))
        bf = {int(a): b for a, b in r['brute'].items()}
        tr, s, kinds, logs, info = theory_row(C)
        g, _, _ = gr_row(C)
        a = 'MATCH' if (s == 'closed' and dict(tr) == bf) else ('FALLBACK' if s != 'closed' else 'MISMATCH')
        b = 'MATCH' if dict(g) == bf else 'MISMATCH'
        st[(k, r['j'], a, b)] += 1
        out.write(json.dumps(dict(file=fn, lift=r['lift'], k=k, j=r['j'], alpha=r['alpha'], old=r['status'], closed=a, gr=b, kinds=kinds)) + "\n")
for k_, v in sorted(st.items(), key=str): print(k_, v)
