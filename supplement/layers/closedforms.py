# Closed forms of RESULT.md checked against the recursive per-residue constructions used by predict.py.
from collections import Counter
import predict as P
def M5_recursive(q,d,kappa):
    # per-residue construction (as in predict.py): residues 0..q-1, h=1 on first q/2, special residue index chosen with h=kappa
    hs=[1]*(q//2)+[0]*(q//2); star=0 if kappa==1 else q-1
    ms=Counter()
    for g in range(q):
        hh=2*hs[g]
        if d==1: ms[1+hh]+=1; continue
        ms[hh]+=q**(d-1)-q**(d-2)
        child=P.S_deg(d-2) if (d>=3 and g==star) else P.S_nd(True,d-2)
        for v,x in child.items(): ms[q*v+hh]+=x
    return P.nz(ms)
def M5_closed(q,d,k):
    if d==1: return Counter({3:q//2,1:q//2})
    if d==2: return P.nz(Counter({2:(q//2)*(q-1),q+2:q//2,q:q//2}))
    S=P.S_deg_closed(d-2); ZS=q**(d-2)-sum(S.values())
    r=Counter()
    r[2]+=(q//2)*(q**(d-1)-q**(d-2))+(q//2-k)*q**(d-2)//2+k*ZS
    r[2*q+2]+=(q//2-k)*q**(d-2)//2
    r[2*q]+=(q//2-1+k)*q**(d-2)//2
    for v,c in S.items(): r[q*v+2*k]+=c
    return P.nz(r)
for q in (8,32):
    P.Q=q; P._memo.clear()
    for d in range(1,9):
        for k in (0,1):
            a=M5_recursive(q,d,k); b=M5_closed(q,d,k)
            assert a==b,(q,d,k,a,b)
            assert sum(v*c for v,c in a.items())==2*q**d
print("M5 closed form OK")
