import sys, itertools
sys.path.insert(0,'..')
from sym import GF
from collections import defaultdict
res={}
for m in map(int,sys.argv[1:]):
    F=GF(m); q=F.q
    U=lambda x: x ^ F.sq(x) ^ F.frob(x,m-1)
    V=lambda x: F.frob(x,2) ^ F.frob(x,m-2)
    bad=set()
    for x in range(2,q): bad.add(F.mul(U(x),F.inv(V(x))))
    inv=F.inv; tr=F.tr; mul=F.mul
    feats={
     'tr1/c':lambda c: tr(inv(c)),
     'trc3':lambda c: tr(F.pow(c,3)),
     'tr1/c3':lambda c: tr(inv(F.pow(c,3))),
     'tr1/(c+1)':lambda c: tr(inv(c^1)),
     'trc/(c+1)^2':lambda c: tr(mul(c,inv(F.sq(c^1)))),
     'trc5':lambda c: tr(F.pow(c,5)),
     'tr1/c5':lambda c: tr(inv(F.pow(c,5))),
     'tr(c+1)^3':lambda c: tr(F.pow(c^1,3)),
     'tr1/(c+1)^3':lambda c: tr(inv(F.pow(c^1,3))),
     'trc7':lambda c: tr(F.pow(c,7)),
    }
    names=list(feats)
    vec={}
    for c in range(2,q):
        if tr(c)!=1: continue
        vec[c]=tuple(feats[n](c) for n in names)
    for k in (1,2,3):
        for S in itertools.combinations(range(len(names)),k):
            cls=defaultdict(lambda:[0,0])
            for c,v in vec.items():
                key=tuple(v[i] for i in S); cls[key][0]+=1; cls[key][1]+= (c not in bad)
            for key,(n,g) in cls.items():
                kk=(tuple(names[i] for i in S),key)
                res.setdefault(kk,[]).append((m,n,g))
cands=[(k,v) for k,v in res.items() if all(n==g and n>0 for (m,n,g) in v)]
for k,v in cands[:30]: print(k,v)
print(len(cands))
best=sorted(res.items(), key=lambda kv: -min(g/n if n else 0 for (m,n,g) in kv[1]))[:10]
for k,v in best: print('best',k,v)
