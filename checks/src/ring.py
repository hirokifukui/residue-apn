import sys; sys.dont_write_bytecode=True
import numpy as np
from collections import Counter
from thmA import P_terms
# GR(2^k,5)=Z_{2^k}[x]/(x^5+x^2+1); full enumeration of all nonzero input differences
def run(k):
    N=1<<k; m=5; n=N**m
    idx=np.arange(n); dig=np.stack([(idx//N**i)%N for i in range(m)],1)
    W=N**np.arange(m)
    def enc(d): return (d%N)@W
    def mul(a,b):
        c=np.zeros((a.shape[0],2*m-1),dtype=np.int64)
        for i in range(m):
            for j in range(m): c[:,i+j]+=a[:,i]*b[:,j]
        for t in range(2*m-2,m-1,-1):
            co=c[:,t].copy(); c[:,t]=0
            c[:,t-5]-=co; c[:,t-3]-=co   # x^t = -x^{t-5}(x^2+1)
        return c[:,:m]%N
    pw={1:dig.copy()}
    def P(e):
        if e in pw: return pw[e]
        h=e//2; r=mul(P(h),P(e-h)); pw[e]=r; return r
    def evalp(coeffs):
        s=np.zeros_like(dig)
        for e,c in coeffs.items(): s=(s+c*P(e))%N
        return enc(s)
    res={}
    for name,co in [('P53',{e:1 for e in P_terms(5,3)}),('D',{5:1,3:1,1:1})]:
        Fv=evalp(co); Fd=dig[Fv]
        perm=len(set(Fv.tolist()))==n
        cls={'G':Counter(),'X':Counter(),'Z':Counter()}
        for a in range(1,n):
            da=dig[a]; rint=int((da%2)@(2**np.arange(m)))
            xi=enc(dig+da); d=enc(Fd[xi]-Fd)
            mx=int(np.bincount(d,minlength=n).max())
            c='Z' if rint==0 else ('X' if rint==1 else 'G')
            cls[c][mx]+=1
        res[name]=dict(perm=perm,**{c:dict(sorted(v.items())) for c,v in cls.items()})
    return res
if __name__=='__main__':
    for k in [2,3]:
        print('k',k,run(k))
