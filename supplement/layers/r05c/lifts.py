# Build test lifts: natural 0/1, A-prescribed (F+2H, Prop. Acontrol of the paper), random 2*,4* perturbations.
import sys, json, random
from grlib import *
from pinv import pinv
def interp(F,vals):
    q=F.q; c={}
    for e in range(q):
        s=0
        for a in range(q):
            v=vals[a]
            if not v: continue
            t=F.pow(a,q-1-e) if (q-1-e)>0 else 1
            if e==0: s^=v^F.mul(v,t)
            else: s^=F.mul(v,t)
        if s: c[e]=s
    return c
def natural(c,m): return [(e,[(v>>i)&1 for i in range(m)]) for e,v in sorted(c.items())]
def A_of(T,m,rho):
    q=1<<m; R8=Ring(m,3); dT=[(e-1,[e*x for x in cd]) for e,cd in T if e>0]
    out=[]
    for a in range(q):
        x=R8.lift(a); y=R8.add(x,R8.lift(rho))
        out.append(res(div(R8.sub(R8.ev(dT,y),R8.ev(dT,x)),2)))
    return out
def set_A(T,m,rho,target):
    F=Field(m); q=F.q; A=A_of(T,m,rho)
    g=[A[a]^target[a] for a in range(q)]
    h=[0]*q
    for a in range(q):
        if a<(a^rho): h[a^rho]=g[a]
    s=[F.sqrt(v) for v in h]
    sc=interp(F,s)
    T2=list(T)+[(2*e+1,[2*((F.mul(v,v)>>i)&1) for i in range(m)]) for e,v in sc.items()]
    assert A_of(T2,m,rho)==target
    return T2
def rand_pert(T,m,rng,nt=6,maxe=40,mults=(2,4)):
    T2=list(T)
    for _ in range(nt):
        e=rng.randrange(0,maxe); mu=rng.choice(mults)
        T2.append((e,[mu*rng.randrange(0,4) for i in range(m)]))
    return T2
