# Sub-case 1 search: merged DEG+DEG pairs (mu=0, c3!=0). Random Taylor perturbations at the DEG centre,
# keeping the pair merged (fix b_3), classify by the Theorem I level data.
import json, sys, random, time
from gr import *
from closed import *
from mklift import *
m=5; idx=json.load(open('lifts/index.json'))
base=sys.argv[1]; k=int(sys.argv[2]); j=int(sys.argv[3]); ub=int(sys.argv[4]); ntr=int(sys.argv[5]); seed=int(sys.argv[6]); out=sys.argv[7]
T0=read_terms(idx[base]['file'],m); R=Ring(m,k); rng=random.Random(seed)
alpha=make_alpha(R,j,ub,seed)
C0=Ctx(T0,m,k,alpha); F=C0.Fd
w=[C0.pi[a]^(F.mul(ub,C0.c3) if j==1 else 0) for a in range(C0.q)]
zs=[a for a in range(C0.q) if w[a]==0]; assert zs, 'no DEG residue'
a=min(zs); xa=C0.center(a)
seen={}
with open(out,'a') as fo:
  for tr in range(ntr):
    bd={s:rand_el(R,rng) for s in range(2,rng.choice([4,6,9])) }
    T1=perturb(T0,R,xa,bd,1)
    C=Ctx(T1,m,k,alpha)
    xb=R.add(xa,C.tau)
    Bv=res(sub_n(C.Rn,C.Tc(xb,R.zero),C.Tc(xa,R.zero),1))
    if Bv:   # fix merging with b_3 (A_F(a) shifts by res(b3)*rho^2)
        corr=F.mul(Bv,F.inv(F.mul(C.rho,C.rho)))
        bd[3]=R.add(bd.get(3,R.zero),R.lift(corr)); T1=perturb(T0,R,xa,bd,1); C=Ctx(T1,m,k,alpha)
        Bv=res(sub_n(C.Rn,C.Tc(xb,R.zero),C.Tc(xa,R.zero),1)); assert Bv==0
    A=Node(C,xa,R.zero,1,2); B=Node(C,xb,R.zero,1,2); log=[]
    try: M=DD(A,B,offset(A,B),log)
    except Fallback as ex: print('fallback',ex); continue
    key=json.dumps([l[1:] for l in log if l[1] in('nonres','res','D=2','D=1')]+[l[1:] for l in log if l[1]=='DN'])
    if key in seen: continue
    fn=f'lifts_r06/s1_{base}_k{k}j{j}u{ub}_{seed}_{tr}.txt'; write_terms(fn,T1); seen[key]=fn
    rec=dict(file=fn,base=base,k=k,j=j,ubar=ub,alpha=R.pack(alpha),a=a,log=log,pred=dict(nz(M)))
    fo.write(json.dumps(rec)+"\n"); fo.flush(); print(tr,key,flush=True)
