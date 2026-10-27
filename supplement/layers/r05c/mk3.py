# Sub-case 3 lifts: DEEP class a (c3=0, pi(a)=0) with w'=c'=0, prescribed (x2,x3) = residues of f_2/4, f_3/4.
import json, sys, random
from gr import *
from mklift import perturb, rand_el
from grlib import write_terms
m=5; idx=json.load(open('lifts/index.json'))
def build(base, a, k, j, ub, x2, x3, seed, extra=True):
    T0=read_terms(idx[base]['file'],m); R=Ring(m,k); rng=random.Random(seed)
    alpha=make_alpha(R,j,ub,seed); C=Ctx(T0,m,k,alpha); xa=C.center(a)
    T1=T0
    if extra:   # random higher Taylor data at x_a
        T1=perturb(T1,R,xa,{s:rand_el(R,rng) for s in range(4,9)},1)
    C=Ctx(T1,m,k,alpha); f=C.taylor(xa)
    assert all(v%2==0 for v in f[2]) and all(v%2==0 for v in f[3])
    t2=R.add(R.smul(4,C.teich[x2]),R.smul(8,rand_el(R,rng)))
    t3=R.add(R.smul(4,C.teich[x3]),R.smul(8,rand_el(R,rng)))
    b2=tuple(((u-v)%R.M)//2 for u,v in zip(t2,f[2])); b3=tuple(((u-v)%R.M)//2 for u,v in zip(t3,f[3]))
    T2=perturb(T1,R,xa,{2:b2,3:b3},1)
    C=Ctx(T2,m,k,alpha); f=C.taylor(xa)
    assert tuple(v%8 for v in f[2])==tuple(v%8 for v in t2) and tuple(v%8 for v in f[3])==tuple(v%8 for v in t3)
    return T2,C,alpha
