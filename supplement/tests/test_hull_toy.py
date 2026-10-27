# test_hull_toy.py (R05c): brute-force check of Propositions hull and hullunit on GR(4,2), n = 2, an MDS layer (B = 3)
# and random residue-preserving permutations G. Checks: max differential probability <= (Dall/q^k)^(B-1) and,
# for inputs with a unit word, <= 2^n (Dunit/q^k)^(B-1). Written by an independent referee instance (Claude), 2026-10-26.
import random, itertools
# GR(4,2) = Z/4[t]/(t^2+t+1); element (a0,a1)
R=[(a,b) for a in range(4) for b in range(4)]
idx={r:i for i,r in enumerate(R)}
def add(x,y): return ((x[0]+y[0])%4,(x[1]+y[1])%4)
def sub(x,y): return ((x[0]-y[0])%4,(x[1]-y[1])%4)
def mul(x,y):
    a0,a1=x;b0,b1=y
    c0=a0*b0; c1=a0*b1+a1*b0; c2=a1*b1  # t^2=-t-1
    return ((c0-c2)%4,(c1-c2)%4)
def res(x): return (x[0]%2,x[1]%2)
def unit(x): return res(x)!=(0,0)
def run(seed):
    random.seed(seed)
    resid=[(0,0),(0,1),(1,0),(1,1)]
    pi=resid[:];random.shuffle(pi)
    G={}
    for a,b in zip(resid,pi):
        cls=[x for x in R if res(x)==a]; tgt=[x for x in R if res(x)==b]; random.shuffle(tgt)
        for x,y in zip(cls,tgt): G[x]=y
    D={}
    for al in R:
        for x in R:
            be=sub(G[add(x,al)],G[x]); D[(al,be)]=D.get((al,be),0)+1
    Du=max(v for (al,be),v in D.items() if unit(al))
    Dall=max(v for (al,be),v in D.items() if al!=(0,0))
    t=(0,1)
    Mm=[[(1,0),(1,0)],[(1,0),t]]
    def Mv(v): return tuple(add(mul(Mm[i][0],v[0]),mul(Mm[i][1],v[1])) for i in range(2))
    V=[(x,y) for x in R for y in R]
    def PS(a,b): return D.get((a[0],b[0]),0)*D.get((a[1],b[1]),0)/256
    worst_u=0;worst=0
    Minv={Mv(v):v for v in V}
    for a in V:
        if a==((0,0),(0,0)): continue
        dist={}
        for x in V:
            p1=PS(a,x)
            if p1==0: continue
            mx=Mv(x)
            for c in V:
                p2=PS(mx,c)
                if p2: dist[c]=dist.get(c,0)+p1*p2
        m=max(dist.values())
        worst=max(worst,m)
        if unit(a[0]) or unit(a[1]): worst_u=max(worst_u,m)
    B=3
    return Du,Dall,worst_u,worst,(Dall/16)**(B-1),4*(Du/16)**(B-1)


import sys
bad=0
for s in range(6):
    Du,Dall,wu,w,b,bu=run(s)
    ok = (w <= b + 1e-12) and (wu <= bu + 1e-12)
    print(s, Du, Dall, round(wu,6), round(w,6), round(b,6), round(bu,6), "ok" if ok else "FAIL")
    bad += (not ok)
if bad: print("HULL_TOY FAIL"); sys.exit(1)
print("HULL_TOY OK 6 seeds")
