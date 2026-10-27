# Generate sub-case 1 lifts (merged DEG+DEG, mu=0, c3!=0) with prescribed Theorem-I level data.
import json, sys, random
from gr import *
from closed import *
import closed; closed.FAST = True
from mklift import perturb, rand_el
from grlib import write_terms
m=5; idx=json.load(open('lifts/index.json'))
def setup(base,k,j,ub,seed):
    T0=read_terms(idx[base]['file'],m); R=Ring(m,k); alpha=make_alpha(R,j,ub,seed)
    C=Ctx(T0,m,k,alpha); F=C.Fd
    w=[C.pi[a]^(F.mul(ub,C.c3) if j==1 else 0) for a in range(C.q)]
    zs=[a for a in range(C.q) if w[a]==0]
    return T0,R,alpha,min(zs)
def merged_fix(T,R,alpha,a,k):
    C=Ctx(T,m,k,alpha); F=C.Fd; xa=C.center(a); xb=R.add(xa,C.tau)
    Bv=res(sub_n(C.Rn,C.Tc(xb,R.zero),C.Tc(xa,R.zero),1))
    if Bv:
        corr=F.mul(Bv,F.inv(F.pow(C.rho,4)))     # A_F(a) moves by res(b_5) rho^4
        T=perturb(T,R,xa,{5:R.lift(corr)},1); C=Ctx(T,m,k,alpha)
        assert res(sub_n(C.Rn,C.Tc(xb,R.zero),C.Tc(xa,R.zero),1))==0
    return T,C
def ddlog(C,a):
    R=C.R; xa=C.center(a); xb=R.add(xa,C.tau)
    A=Node(C,xa,R.zero,1,2); B=Node(C,xb,R.zero,1,2); log=[]
    M=DD(A,B,offset(A,B),log); return log,M
def search(base,k,j,ub,seed,pred,tries=3000,params=None):
    """random-walk + coordinate scan until pred(log) holds."""
    T0,R,alpha,a=setup(base,k,j,ub,seed); rng=random.Random(seed)
    T,C=merged_fix(perturb(T0,R,Ctx(T0,m,k,alpha).center(a),{s:rand_el(R,rng) for s in range(2,9)},1),R,alpha,a,k)
    if params is None: params=[(s,t) for t in (1,2,3,4) for s in (2,4,5,6,7,8,9,10)]
    best=None
    for it in range(tries):
        try: log,M=ddlog(C,a)
        except Fallback: log=None
        if log is not None:
            sc=pred(log)
            if sc is True: return T,C,a,log,M,alpha
        s,t=params[rng.randrange(len(params))]
        T1,C1=merged_fix(perturb(T,R,C.center(a),{s:R.lift(rng.randrange(1,32))},t),R,alpha,a,k)
        # greedy acceptance on partial score
        try: l1,_=ddlog(C1,a); s1=pred(l1)
        except Fallback: continue
        s0=pred(log) if log is not None else -1
        if s1 is True or (isinstance(s1,int) and isinstance(s0,int) and s1>=s0) or rng.random()<0.05:
            T,C=T1,C1
    return None
