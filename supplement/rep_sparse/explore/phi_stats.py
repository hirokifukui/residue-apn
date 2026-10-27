import sys
sys.path.insert(0,'.')
from sym import GF
for m in map(int, sys.argv[1:]):
    F=GF(m); q=F.q
    def U(x): return x ^ F.sq(x) ^ F.frob(x, m-1)
    def V(x): return F.frob(x,2) ^ F.frob(x, m-2)
    N1=0; vals={}
    for x in range(2,q):
        c=F.mul(U(x),F.inv(V(x)))
        vals.setdefault(c,[]).append(x)
        N1+=F.tr(c)
    bad1=sum(1 for c in vals if F.tr(c)==1)
    from collections import Counter
    print(m, 'q/2',q//2,'N1',N1,'bad_Tr1',bad1, 'fiber sizes', Counter(len(v) for v in vals.values()), 'c=0 bad?', 0 in vals)
