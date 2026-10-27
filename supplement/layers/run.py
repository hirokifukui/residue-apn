# Driver: brute force (redspec, Lemma R only) vs theory prediction, for given k and lifts.
import sys, json, random, subprocess, time
from grlib import *
from predict import predict
from lifts import A_of
from pinv import pinv
m=5; q=32; Fd=Field(m)
k=int(sys.argv[1]); names=sys.argv[2].split(','); out=sys.argv[3]
js=[int(x) for x in sys.argv[4].split(',')] if len(sys.argv)>4 else list(range(1,k-2))
maxj1=int(sys.argv[5]) if len(sys.argv)>5 else 99
idx=json.load(open('lifts/index.json'))
rng=random.Random(hash((k,sys.argv[2]))&0xffff)
R=Ring(m,k)
def pick_u(T,P):
    A=A_of(T,m,P['rho']); pi=P['pi']; c3=P['c3']; mu=P['mu']
    seen={}; 
    for u in range(1,q):
        w0=any(pi[a]^Fd.mul(u,c3)==0 for a in range(q))
        Bz=[a for a in range(q) if A[a]^Fd.mul(u,mu)==0]
        md=any(pi[a]^Fd.mul(u,c3)==0 or pi[a^P['rho']]^Fd.mul(u,c3)==0 for a in Bz)
        key=(w0,len(Bz)>0,md)
        seen.setdefault(key,[]).append(u)
    us=[rng.choice(v) for v in seen.values()]
    return us
with open(out,'a') as fo:
  for nm in names:
    T=read_terms(idx[nm]['file'],m); c=residue_coeffs(T,m); P=pinv(c,m)
    alphas=[]
    for j in js:
        if j>k-3: continue
        us=pick_u(T,P)[:maxj1] if j==1 else [rng.randrange(1,q) for _ in range(2)]
        for u in us:
            hi=tuple(rng.randrange(0,1<<(k-j)) for _ in range(m))
            uu=R.add(R.lift(u),R.smul(2,hi))
            alphas.append(R.pack(R.smul(1<<j,uu)))
    open('_al.txt','w').write("\n".join(map(str,alphas))+"\n")
    t0=time.time()
    o=subprocess.run(['./redspec2',str(m),str(k),'37',idx[nm]['file'],'_al.txt'],capture_output=True,text=True).stdout
    tb=time.time()-t0
    for line in o.strip().split('\n'):
        a=int(line.split()[1]); j=int(line.split()[3])
        bf={int(x.split('x')[0]):int(x.split('x')[1]) for x in line.split('|')[1].split()}
        tot,un,info=predict(T,m,k,R.unpack(a))
        pred={int(v):c for v,c in tot.items()}
        status='MATCH' if (not un and pred==bf) else ('UNPREDICTED' if un else 'MISMATCH')
        if info['checks']: status+='+CHECKFAIL'
        rec=dict(lift=nm,k=k,alpha=a,j=j,ubar=info['ubar'],status=status,brute=bf,pred=pred if not un else None,unpred=[list(map(str,x)) for x in un],
                 B_zero=info['B_zero'],w_zero=info['w_zero'],kappa=info.get('kappa'),ptypes=info.get('ptypes'),DD2_s=info.get('DD2_s'),deep={str(a):v for a,v in info.get('deep',{}).items()},checks=info['checks'])
        fo.write(json.dumps(rec)+"\n"); fo.flush()
        print(nm,k,j,info['ubar'],status,bf if status!='MATCH' else '',un if un else '',flush=True)
    print(f'# {nm} brute {tb:.1f}s',flush=True)
