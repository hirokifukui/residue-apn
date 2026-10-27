import sys
sys.path.insert(0,'..')
from sym import *
def Bop(F,c):
    m=F.m; return {m-2:1,m-1:1,0:1,1:1,2:c}
def apply(F,op,x):
    s=0
    for k,a in op.items(): s^=F.mul(a,F.frob(x,k))
    return s
for m in map(int,sys.argv[1:]):
    F=GF(m); q=F.q; shown=0; dims={}
    for c in range(2,q):
        B=Bop(F,c)
        if not lin_invertible(F,B): continue
        # rho = B^{-1}(1)
        rho=[x for x in range(q) if apply(F,B,x)==1][0] if m<=11 else None
        sq=lambda a: F.frob(a,m-1)
        K=lambda y: apply(F,B,y)^F.sq(apply(F,B,y))
        Lp=lambda a: K(sq(F.mul(a,rho)))^F.mul(rho,K(a))
        cols=[Lp(1<<i) for i in range(m)]
        r=rank(cols,m); dims[r]=dims.get(r,0)+1
        # dual: lambda with Tr(lambda*Lp(e_i))=0 all i
        duals=[l for l in range(1,q) if all(F.tr(F.mul(l,v))==0 for v in cols)]
        if shown<4:
            cand={'1':1,'rho':rho,'1/rho':F.inv(rho),'rho2':F.sq(rho),'c':c,'1/(1+rho)':F.inv(1^rho) if rho!=1 else 0}
            hit=[n for n,v in cand.items() if v in duals]
            print(m,'c',c,'rho',rho,'rank',r,'duals',duals[:6],'hits',hit)
            shown+=1
    print(m,'rank distribution',dims)
