# p = L(A^3), A = S_u = u x^{1/2} + x + x^2, L = l_{-1} y^{1/2} + l_0 y + l_1 y^2 with M(u)=0 and mu=0
import sys
sys.path.insert(0,'.')
from sym import *
from collections import Counter
for m in map(int, sys.argv[1:]):
    F=GF(m); q=F.q; mul=F.mul; inv=F.inv
    sq=lambda a: F.frob(a,m-1)
    cnt=Counter(); good=[]
    for u in range(2,q):
        su=sq(u); u2=mul(u,u); u3=mul(u2,u); u4=mul(u2,u2); u6=mul(u4,u2)
        # eq1 (mu): l_{-1} su + l_0 (u+u2) + l_1 (u6+u4) = 0
        # eq2 (M(u)): l_{-1}(su+u) + l_0(u2+u3) + l_1 u6 = 0
        r1=(su, u^u2, u6^u4); r2=(su^u, u2^u3, u6)
        # cross product gives solution
        l=(mul(r1[1],r2[2])^mul(r1[2],r2[1]), mul(r1[2],r2[0])^mul(r1[0],r2[2]), mul(r1[0],r2[1])^mul(r1[1],r2[0]))
        if l==(0,0,0): cnt['degenerate']+=1; continue
        A={m-1:u,0:1,1:1}; L={m-1:l[0],0:l[1],1:l[2]}
        Li={k:v for k,v in L.items() if v}
        ia=lin_invertible(F,A); il=lin_invertible(F,Li)
        if not (ia and il): cnt[('invA',ia,'invL',il)]+=1; continue
        iv=invariants(F,*expand_LA3(F,A,Li))
        if not iv['H']: cnt['noH:'+iv['why']]+=1; continue
        key=(iv['rho']==1, iv['mu']==0, iv['z'])
        cnt[key]+=1
        if key==(True,True,0): good.append(u)
    print(m, dict(cnt), len(good), good[:10], flush=True)
