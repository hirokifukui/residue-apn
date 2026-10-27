# Consolidate all result files: re-run the (Python-only) predictor where pair-type labels are missing,
# re-check status against the stored brute-force spectra, and write summary.json.
import json, glob, sys
from collections import Counter, defaultdict
from grlib import *
from predict import predict
idx=json.load(open('lifts/index.json'))
rows=[]
for fn in sorted(glob.glob('res_*.jsonl')):
    if 'test' in fn: continue
    for l in open(fn):
        r=json.loads(l); r['file']=fn; rows.append(r)
cache={}
out=[]
for r in rows:
    m=r.get('m',5)
    if not r.get('ptypes') or r['status']=='MISMATCH':
        fnm=idx[r['lift']]['file'] if r['lift'] in idx else r['lift']
        T=read_terms(fnm,m); R=Ring(m,r['k'])
        tot,un,info=predict(T,m,r['k'],R.unpack(r['alpha']))
        pred={int(v):c for v,c in tot.items()}
        bf={int(v):c for v,c in r['brute'].items()}
        st='MATCH' if (not un and pred==bf) else ('UNPREDICTED' if un else 'MISMATCH')
        r['status2']=st; r['ptypes']=info['ptypes']
    else:
        r['status2']=r['status'].replace('+CHECKFAIL','')
    out.append(r)
byk=Counter((r['k'],r['j'],r['status2']) for r in out)
types=defaultdict(Counter)
for r in out:
    for t,c in r['ptypes'].items(): types[t][r['status2']]+=1
unp=Counter()
for r in out:
    for u in r.get('unpred',[]): unp[str(u[0])+':'+'+'.join(sorted(u[2:4])) if len(u)>3 else str(u)]+=1
summ=dict(rows=len(out),lifts=len(set(r['lift'] for r in out)),by_k_j_status={f'k={k} j={j} {s}':c for (k,j,s),c in sorted(byk.items())},
          pairtype_rows={t:dict(c) for t,c in sorted(types.items())},checkfails=sum(1 for r in out if 'CHECKFAIL' in r['status']),
          mismatches=[(r['lift'],r['k'],r['alpha']) for r in out if r['status2']=='MISMATCH'])
json.dump(summ,open('summary.json','w'),indent=1)
print(json.dumps(summ,indent=1))
