# Targeted rows: run_rows.py k out spec...   spec = lift:j:ubar[:seed]
import sys, json, random, subprocess, time
from grlib import *
from predict import predict
m=5;q=32
k=int(sys.argv[1]); out=sys.argv[2]
idx=json.load(open('lifts/index.json')); R=Ring(m,k)
with open(out,'a') as fo:
  for spec in sys.argv[3:]:
    p=spec.split(':'); nm=p[0]; j=int(p[1]); ub=int(p[2]); seed=int(p[3]) if len(p)>3 else 1
    rng=random.Random(seed)
    hi=tuple(rng.randrange(0,1<<(k-j)) for _ in range(m))
    a=R.pack(R.smul(1<<j,R.add(R.lift(ub),R.smul(2,hi))))
    open(f'_al_{k}.txt','w').write(f"{a}\n")
    t0=time.time()
    o=subprocess.run(['./redspec2',str(m),str(k),'37',idx[nm]['file'],f'_al_{k}.txt'],capture_output=True,text=True).stdout.strip()
    tb=time.time()-t0
    bf={int(x.split('x')[0]):int(x.split('x')[1]) for x in o.split('|')[1].split()}
    T=read_terms(idx[nm]['file'],m)
    tot,un,info=predict(T,m,k,R.unpack(a))
    pred={int(v):c for v,c in tot.items()}
    status='MATCH' if (not un and pred==bf) else ('UNPREDICTED' if un else 'MISMATCH')
    if info['checks']: status+='+CHECKFAIL'
    rec=dict(lift=nm,k=k,alpha=a,j=j,ubar=info['ubar'],status=status,brute=bf,pred=pred if not un else None,unpred=[list(map(str,x)) for x in un],
             B_zero=info['B_zero'],w_zero=info['w_zero'],kappa=info.get('kappa'),ptypes=info.get('ptypes'),DD2_s=info.get('DD2_s'),checks=info['checks'],brute_seconds=round(tb,1))
    fo.write(json.dumps(rec)+"\n"); fo.flush()
    print(nm,k,j,ub,status,f'{tb:.0f}s',bf,info.get('kappa'),info.get('ptypes'),flush=True)
