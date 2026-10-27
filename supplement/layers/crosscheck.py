# Cross-check: reduced brute force (redspec2, uses Lemma R) == full-table brute force (rowspec, no reduction).
import subprocess,random,sys,json
from grlib import *
k=int(sys.argv[1]); names=sys.argv[2].split(',')
R=Ring(5,k); rng=random.Random(5)
als=[]
for j in range(1,k):
    for _ in range(2 if j>1 else 4):
        u=R.add(R.lift(rng.randrange(1,32)),R.smul(2,tuple(rng.randrange(1<<(k-1)) for _ in range(5))))
        als.append(R.pack(R.smul(1<<j,u)))
open('alx.txt','w').write("\n".join(map(str,als))+"\n")
res={}
for nm in names:
    a=subprocess.run(['./redspec2','5',str(k),'37',f'lifts/{nm}.txt','alx.txt'],capture_output=True,text=True).stdout.strip().split('\n')
    b=subprocess.run(['./rowspec','5',str(k),'37',f'lifts/{nm}.txt','alx.txt'],capture_output=True,text=True).stdout.strip().split('\n')
    ok=len(a)==len(b)==len(als) and all(x.split('|')[1]==y.split('|')[1] for x,y in zip(a,b))
    res[nm]=dict(rows=len(als),agree=ok); print(nm,ok,len(als),flush=True)
json.dump(res,open(f'crosscheck_k{k}.json','w'))
