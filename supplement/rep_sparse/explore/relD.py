import sys
sys.path.insert(0,'..')
from sym import GF
from collections import Counter
m=int(sys.argv[1]); F=GF(m); q=F.q
h=lambda z: F.pow(z,15)^F.pow(z,14)^F.pow(z,12)^F.pow(z,8)
fib={}
for z in range(1,q): fib.setdefault(h(z),[]).append(z)
# kernel elements y = 1/z
rels=Counter()
for c,zs in fib.items():
    if len(zs)<3: continue
    ys=[F.inv(z) for z in zs]
    # test relations among ys: y2 = y1^(2^k) ; y2 = y1^k for small k; y2 = y1*const in F_4? ; y1*y2 =1 ; y1+y2 = y1^2 ...
    for a in ys:
        for b in ys:
            if a==b: continue
            for k in range(1,m):
                if F.frob(a,k)==b: rels['frob%d'%k]+=1
            for e in range(2,40):
                if F.pow(a,e)==b: rels['pow%d'%e]+=1
            if F.mul(a,b)==1: rels['inv']+=1
            if F.sq(a)^a==b: rels['a2+a']+=1
            if F.sq(a)==b^1: rels['a2+1']+=1
print(m, len([1 for zs in fib.values() if len(zs)>=3]), rels)
