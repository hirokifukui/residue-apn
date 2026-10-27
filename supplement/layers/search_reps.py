# Search quadratic APN permutations p = L(A(x)^3) satisfying (H); classify by (mu, c3, pi zeros, Z).
import sys, random, json
from grlib import *
from pinv import pinv
def interp(F,vals):
    q=F.q; c={}
    # p(X)=sum_a v(a)(1-(X-a)^{q-1}) ; coefficient of X^e
    from math import comb
    for e in range(q):
        s=0
        for a in range(q):
            v=vals[a]
            if not v: continue
            # (X+a)^{q-1} = sum_e C(q-1,e) X^e a^{q-1-e}, C(q-1,e) odd for all e
            t=F.pow(a,q-1-e) if (q-1-e)>0 else 1
            if e==0: s^=v^F.mul(v,t)   # 1 - (..)
            else: s^=F.mul(v,t)
        if s: c[e]=s
    return c
def randlin(m,rng):
    while True:
        cols=[rng.randrange(1,1<<m) for _ in range(m)]
        # check invertible
        img=set([0])
        for cl in cols: img|={x^cl for x in img}
        if len(img)==1<<m: return cols
def applylin(cols,x):
    r=0;i=0
    while x:
        if x&1: r^=cols[i]
        x>>=1;i+=1
    return r
if __name__=="__main__":
    m=int(sys.argv[1]); n=int(sys.argv[2]); seed=int(sys.argv[3]); rng=random.Random(seed)
    F=Field(m); q=F.q; seen={}
    for t in range(n):
        A=randlin(m,rng); L=randlin(m,rng)
        vals=[applylin(L,F.pow(applylin(A,x),3)) for x in range(q)]
        c=interp(F,vals)
        if c.get(0): c.pop(0)  # drop constant (does not affect anything) -> keep p(0)=0 for simplicity
        try: d=pinv(c,m)
        except AssertionError as e: continue
        key=(d['mu']==0,d['c3']==0,len(d['pi_zeros'])>0,len(d['Z'])>0)
        if key not in seen:
            seen[key]=dict(coeffs=c,**{k:v for k,v in d.items() if k!='pi'})
            print(key, json.dumps(seen[key]),flush=True)
    json.dump({str(k):v for k,v in seen.items()},open(f'reps_m{m}.json','w'))
