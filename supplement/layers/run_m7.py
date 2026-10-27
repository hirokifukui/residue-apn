# Rows for m=7 files given by path: run_m7.py k out spec...  spec=path:j:ubar
import sys, json, random, subprocess, time
from grlib import *
from predict import predict
m=7; k=int(sys.argv[1]); out=sys.argv[2]; R=Ring(m,k)
with open(out,'a') as fo:
  for spec in sys.argv[3:]:
    path,j,ub=spec.split(':'); j=int(j); ub=int(ub); rng=random.Random(ub)
    hi=tuple(rng.randrange(0,1<<(k-j)) for _ in range(m))
    a=R.pack(R.smul(1<<j,R.add(R.lift(ub),R.smul(2,hi))))
    open('_al_m7.txt','w').write(f"{a}\n"); t0=time.time()
    o=subprocess.run(['./redspec2',str(m),str(k),'131',path,'_al_m7.txt'],capture_output=True,text=True).stdout.strip()
    tb=time.time()-t0
    bf={int(x.split('x')[0]):int(x.split('x')[1]) for x in o.split('|')[1].split()}
    T=read_terms(path,m); tot,un,info=predict(T,m,k,R.unpack(a))
    pred={int(v):c for v,c in tot.items()}
    status='MATCH' if (not un and pred==bf) else ('UNPREDICTED' if un else 'MISMATCH')
    if info['checks']: status+='+CHECKFAIL'
    rec=dict(m=7,lift=path,k=k,alpha=a,j=j,ubar=info['ubar'],status=status,brute=bf,pred=pred if not un else None,unpred=[list(map(str,x)) for x in un],ptypes=info.get('ptypes'),checks=info['checks'],brute_seconds=round(tb,1))
    fo.write(json.dumps(rec)+"\n"); fo.flush()
    print(path,k,j,ub,status,f'{tb:.0f}s',bf,info.get('ptypes'),flush=True)
