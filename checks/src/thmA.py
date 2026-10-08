import sys; sys.dont_write_bytecode=True
from gf import GF
import numpy as np, json
from math import gcd
from collections import Counter
def P_terms(m,r):
    q=1<<m; c=Counter()
    for i in range(r):
        for j in range(r): c[2**(i+1)+2**j]+=1
    T3={e for e,v in c.items() if v%2}
    c2=Counter()
    for e in T3:
        f=(e*2**(m-2))%(q-1)
        if f==0: f=q-1
        c2[f]+=1
    return {e for e,v in c2.items() if v%2}
def gpt_identity(m,r):
    V=[2**i for i in range(r-2)]; W=2**(r-2); Y=2**(m-2); Z=2**(m-1)
    S=V+[W]; c=Counter()
    for e in S: c[e]+=1
    for e in S: c[Y+e]+=1
    c[Z+Y]+=1; c[Z+W]+=1
    for e in V: c[W+e]+=1
    return c
def adm(m): return [r for r in range(3,m,2) if gcd(r,m)==1]
if __name__=="__main__":
    bad=0;n=0
    for m in range(5,102,2):
        for r in adm(m):
            n+=1
            P=P_terms(m,r); c=gpt_identity(m,r); q=1<<m
            ok = all(v==1 for v in c.values()) and set(c)==P and len(P)==3*r-2 and max(P)==3*q//4
            der=Counter(e-1 for e in P if e%2)
            ok = ok and set(der)=={0,2**(m-2),2**(r-2)} and all(v==1 for v in der.values())
            if not ok: bad+=1
    print("formula pairs",n,"bad",bad)
    for m in [5,7,9,11,13]:
        F=GF(m); q=F.q; X=F.X
        for r in adm(m)+([3] if m==9 else []):
            T=np.zeros(q,dtype=np.int64)
            for i in range(r): T^=F.pw(X,2**i)
            comp=F.pw(F.pw(T,3),2**(m-2))
            P=P_terms(m,r); val=F.poly(P)
            eq=bool((val==comp).all())
            img=len(set(val.tolist()))
            seen=set(); maxd=0
            for a in range(1,q):
                if a in seen: continue
                x=a
                for _ in range(m): seen.add(x); x=int(F.mul(x,x))
                d=val[X^a]^val
                cnt=Counter(d.tolist()); maxd=max(maxd,max(cnt.values()))
            dv=F.poly({0,2**(m-2),2**(r-2)})
            dc=Counter(dv.tolist())
            opt = (0 not in dc) and set(dc.values())=={2}
            d1=set((val[X^1]^val).tolist()); tr1=set(np.nonzero(F.tr(X)==1)[0].tolist())
            rec=dict(m=m,r=r,terms=len(P),eq=eq,perm=img==q,img=img,maxDDT=maxd,opt=opt,d1_is_tr1=d1==tr1)
            if m<=9:
                mx=0
                for v in range(1,q):
                    f=F.tr(F.mul(v,val))
                    h=(1-2*f).astype(np.int64); hh=1
                    while hh<q:
                        h=h.reshape(-1,2*hh); a=h[:,:hh].copy(); b=h[:,hh:].copy()
                        h=np.concatenate([a+b,a-b],axis=1).reshape(-1); hh*=2
                    mx=max(mx,int(np.abs(h).max()))
                rec['walsh_max']=mx
            print(rec)
