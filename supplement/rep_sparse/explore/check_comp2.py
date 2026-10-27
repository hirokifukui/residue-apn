import sys
sys.path.insert(0,'..')
from sym import *
from collections import Counter
m=int(sys.argv[1]); F=GF(m); cnt=Counter(); good=[]
def compose(Bc, Cc):
    # operators as dict pos->coef (pos in Z); (b sigma^i) o (c sigma^j) = b c^{2^i} sigma^{i+j}
    R={}
    for i,b in Bc.items():
        for j,c in Cc.items():
            R[i+j]=R.get(i+j,0)^F.mul(b,F.frob(c,i%m))
    return {k:v for k,v in R.items() if v}
for line in open(sys.argv[2]):
    u,th,v=map(int,line.split())
    Su={-1:u,0:1,1:1}; Sv={-1:v,0:1,1:1}
    A=compose(Su,compose({0:th},Sv))
    Am={}
    for k,c in A.items(): Am[k%m]=Am.get(k%m,0)^c
    iu=lin_invertible(F,Su and {k%m:c for k,c in Su.items()}); iv_=lin_invertible(F,{k%m:c for k,c in Sv.items()})
    inv=lin_invertible(F,Am)
    if not inv: cnt[('noninv',iu,iv_)]+=1; continue
    I=invariants(F,*expand_LA3(F,Am,{0:1}))
    if not I['H']: cnt[('inv',iu,iv_,'noH',I['why'])]+=1; continue
    key=('inv',iu,iv_,'rho1',I['rho']==1,'mu0',I['mu']==0,'z',I['z'])
    cnt[key]+=1
    if I['mu']==0 and I['z']==0: good.append((u,th,v))
for k,v in sorted(cnt.items(),key=str): print(k,v)
print('good',len(good),good[:5])
