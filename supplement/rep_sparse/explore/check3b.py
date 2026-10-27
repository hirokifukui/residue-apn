import sys
sys.path.insert(0,'..')
from sym import *
from collections import Counter
m=int(sys.argv[1]); F=GF(m)
def compose(B,C):
    R={}
    for i,b in B.items():
        for j,c in C.items():
            R[i+j]=R.get(i+j,0)^F.mul(b,F.frob(c,i%m))
    return {k:v for k,v in R.items() if v}
cnt=Counter(); us=set(); ex=[]
for line in open(sys.argv[2]):
    u,t1,t2=map(int,line.split())
    S={-1:u,0:1,1:1}
    A=compose(S,compose({0:t1},compose(S,compose({0:t2},S))))
    Am={}
    for k,c in A.items(): Am[k%m]=Am.get(k%m,0)^c
    Am={k:v for k,v in Am.items() if v}
    if not lin_invertible(F,Am): cnt['noninv']+=1; continue
    I=invariants(F,*expand_LA3(F,Am,{0:1}))
    key=(I['H'], I.get('mu')==0, I.get('z'))
    cnt[key]+=1
    if key==(True,True,0): us.add(u); ex.append((u,t1,t2,len(expand_LA3(F,Am,{0:1})[0])+len(expand_LA3(F,Am,{0:1})[1])))
print(m, dict(cnt), 'distinct u', len(us), ex[:3])
