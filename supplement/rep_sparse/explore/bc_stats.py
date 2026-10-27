import sys
sys.path.insert(0,'..')
from sym import GF
from collections import Counter
for m in map(int,sys.argv[1:]):
    F=GF(m); q=F.q
    h=lambda z: F.pow(z,15)^F.pow(z,14)^F.pow(z,12)^F.pow(z,8)
    fib={}
    for z in range(1,q): fib.setdefault(h(z),[]).append(z)
    sizes=Counter(len(v) for v in fib.values())
    inj=q-len(fib)
    big=[ (c,v) for c,v in fib.items() if len(v)>=3][:3]
    print(m,'#inj',inj,'fibers',dict(sizes),'c=1 inj', 1 not in fib, 'examples',big, flush=True)
