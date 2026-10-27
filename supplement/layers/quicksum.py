import json,glob
from collections import Counter,defaultdict
rows=[]
for fn in sorted(glob.glob('res_k*.jsonl'))+glob.glob('res_m7.jsonl'):
    for l in open(fn): r=json.loads(l); r['file']=fn; rows.append(r)
st=lambda r:r['status'].replace('+CHECKFAIL','')
by=Counter((r['k'],r['j'],st(r)) for r in rows)
pt=defaultdict(Counter)
for r in rows:
    for t in (r.get('ptypes') or {}): pt[t][st(r)]+=1
un=Counter()
for r in rows:
    for u in r.get('unpred',[]): un[' '.join(u[2:4]) if u[0]=='merged' else u[0]]+=1
kap=Counter(v for r in rows if r.get('kappa') for v in r['kappa'].values())
S=dict(rows=len(rows),lifts=len(set(r['lift'] for r in rows)),by_k_j_status={f'k={k} j={j} {s}':c for (k,j,s),c in sorted(by.items())},pairtypes_seen={t:dict(c) for t,c in sorted(pt.items())},unpredicted_reasons=dict(un),checkfail_rows=sum('CHECKFAIL' in r['status'] for r in rows),kappa_values=dict(kap),mismatches=[(r['lift'],r['k'],r['alpha']) for r in rows if st(r)=='MISMATCH'])
json.dump(S,open('summary.json','w'),indent=1); print(json.dumps(S,indent=1))
