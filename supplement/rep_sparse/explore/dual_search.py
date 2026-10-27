import sys, itertools
sys.path.insert(0,'..')
from sym import *
def apply(F,op,x):
    s=0
    for k,a in op.items(): s^=F.mul(a,F.frob(x,k))
    return s
res={}
for m in (7,9):
    F=GF(m); q=F.q
    inst=0
    for c in range(2,q):
        B={m-2:1,m-1:1,0:1,1:1,2:c}
        if not lin_invertible(F,B): continue
        rho=[x for x in range(q) if apply(F,B,x)==1][0]
        sq=lambda a: F.frob(a,m-1)
        K=lambda y: apply(F,B,y)^F.sq(apply(F,B,y))
        cols=[K(sq(F.mul(1<<i,rho)))^F.mul(rho,K(1<<i)) for i in range(m)]
        if rank(cols,m)!=m-1: continue
        lam=[l for l in range(1,q) if all(F.tr(F.mul(l,v))==0 for v in cols)][0]
        inst+=1
        def P(x,e): return F.pow(x,e%(q-1)) if x else 0
        for i,j,k,l in itertools.product(range(-4,5),repeat=4):
            v=F.mul(F.mul(P(rho,i),P(rho^1,j)),F.mul(P(c,k),P(c^1,l)))
            key=(i,j,k,l)
            # allow Frobenius twists of lambda
            ok=any(F.frob(lam,t)==v for t in range(m))
            res.setdefault(key,[0,0]); res[key][0]+=1; res[key][1]+=ok
        if inst>=12: break
good=[k for k,v in res.items() if v[0]==v[1]]
print('always-dual monomials (up to Frobenius):',good[:20])
