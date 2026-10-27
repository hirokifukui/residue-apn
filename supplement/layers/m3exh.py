import itertools
from grlib import Field
F=Field(3);q=8
X=list(range(8))
P={e:[F.pow(x,e) if e else 1 for x in X] for e in range(7)}
cnt=0;found=[]
for c1,c3,c5 in itertools.product(range(8),repeat=3):
    dp=[c1^F.mul(c3,P[2][x])^F.mul(c5,P[4][x]) for x in X]
    if 0 in dp: continue
    for c2,c4,c6 in itertools.product(range(8),repeat=3):
        c={1:c1,2:c2,3:c3,4:c4,5:c5,6:c6}
        p=[0]*8
        for e,v in c.items():
            if v:
                for x in X: p[x]^=F.mul(v,P[e][x])
        if len(set(p))<8: continue
        ok=True
        for d in range(1,8):
            s=set(p[x^d]^p[x] for x in X)
            if len(s)!=4: ok=False;break
        if ok: cnt+=1; found.append(c)
print("quadratic APN perms with zero-free p':",cnt, found[:3])
