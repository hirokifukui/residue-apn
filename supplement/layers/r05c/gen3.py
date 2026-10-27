# Sub-case 3 lifts: DEEP class with w'=c'=0, prescribed L-type, merged/split as requested.
import json, sys, random
from gr import *
from mklift import perturb, rand_el
from grlib import write_terms
from pinv import peval
from closed import Node, shape
m=5; idx=json.load(open('lifts/index.json'))
def build(base, a, k, j, ub, mode, merge, seed):
    T0=read_terms(idx[base]['file'],m); R=Ring(m,k); rng=random.Random(seed)
    alpha=make_alpha(R,j,ub,seed); C=Ctx(T0,m,k,alpha); F=C.Fd; xa=C.center(a)
    c5=C.c5; p4=peval(F,C.pc,a,4); u=C.ubar
    # choose target (lam1, lam2)
    if mode=='H0':   # lam1!=0, L bijective
        while True:
            l1,l2=rng.randrange(1,32),rng.randrange(0,32)
            if len({F.mul(l1,y)^F.mul(l2,F.mul(y,y))^F.mul(c5,F.pow(y,4)) for y in range(32)})==32: break
    elif mode=='H1':
        while True:
            l1,l2=rng.randrange(1,32),rng.randrange(0,32)
            if len({F.mul(l1,y)^F.mul(l2,F.mul(y,y))^F.mul(c5,F.pow(y,4)) for y in range(32)})==16: break
    elif mode=='H2':
        while True:
            u1,u2=rng.randrange(1,32),rng.randrange(1,32)
            if u1!=u2:
                s=F.mul(u1,u1)^F.mul(u1,u2)^F.mul(u2,u2); l2=F.mul(c5,s); l1=F.mul(c5,F.mul(F.mul(u1,u2),u1^u2))
                if l1: break
    elif mode=='Z1': l1,l2=0,rng.randrange(1,32)
    elif mode=='Z2': l1,l2=0,0
    # solve x3, x2
    if j==1:
        x3=l2^F.mul(u,p4); x2=l1^F.mul(u,x3)^F.mul(F.pow(u,3),c5)
    else: x3,x2=l2,l1
    T1=perturb(T0,R,xa,{s:rand_el(R,rng) for s in range(4,10)},1)
    C=Ctx(T1,m,k,alpha); f=C.taylor(xa)
    t2=R.add(R.smul(4,C.teich[x2]),R.smul(8,rand_el(R,rng))); t3=R.add(R.smul(4,C.teich[x3]),R.smul(8,rand_el(R,rng)))
    b2=tuple(((x-y)%R.M)//2 for x,y in zip(t2,f[2])); b3=tuple(((x-y)%R.M)//2 for x,y in zip(t3,f[3]))
    T2=perturb(T1,R,xa,{2:b2,3:b3},1); C=Ctx(T2,m,k,alpha)
    # merging: B(a) = res((T(x_b)-T(x_a))/2); shift with b_5 (A_F(a) moves by res(b5) rho^4)
    xb=R.add(xa,C.tau); Bv=res(sub_n(C.Rn,C.Tc(xb,R.zero),C.Tc(xa,R.zero),1))
    want0=(merge=='merged')
    if want0 and Bv: tgt=Bv
    elif (not want0) and Bv==0: tgt=rng.randrange(1,32)
    else: tgt=None
    if tgt is not None:
        T2=perturb(T2,R,xa,{5:R.lift(F.mul(tgt,F.inv(F.pow(C.rho,4))))},1); C=Ctx(T2,m,k,alpha)
        Bv=res(sub_n(C.Rn,C.Tc(xb,R.zero),C.Tc(xa,R.zero),1)); assert (Bv==0)==want0
    f=C.taylor(xa); assert tuple(v%8 for v in f[2])==tuple(v%8 for v in t2) and tuple(v%8 for v in f[3])==tuple(v%8 for v in t3)
    Psi=Node(C,xa,R.zero,1,4)
    if Psi.D>=1:
        co=shape(Psi); assert co.get(1,0)==l1 and co.get(2,0)==l2 and co.get(4,0)==c5, (co,l1,l2,c5)
    return T2,C,alpha,dict(l1=l1,l2=l2,c5=c5,x2=x2,x3=x3)
if __name__=='__main__':
    jobs=json.loads(sys.argv[1]); out=sys.argv[2]
    for base,a,k,j,ub,mode,merge,seed in jobs:
        T,C,alpha,info=build(base,a,k,j,ub,mode,merge,seed)
        fn=f'lifts_r06/s3_{base}_a{a}_k{k}j{j}u{ub}_{mode}_{merge}_s{seed}.txt'; write_terms(fn,T)
        rec=dict(file=fn,k=k,j=j,ubar=ub,alpha=C.R.pack(alpha),a=a,mode=mode,merge=merge,info=info)
        open(out,'a').write(json.dumps(rec)+"\n"); print('OK',fn,info,flush=True)
