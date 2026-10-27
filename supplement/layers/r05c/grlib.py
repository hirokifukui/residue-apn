# Galois ring / field helpers for the intermediate-layer study (independent of r07 code).
import random
POLYS={3:0b1011,5:0b100101,7:0b10000011}
class Field:
    def __init__(s,m):
        s.m=m; s.q=1<<m; s.P=POLYS[m]
        s.mt=[[0]*s.q for _ in range(s.q)]
        for a in range(s.q):
            for b in range(s.q):
                r=0;x=a;y=b
                while y:
                    if y&1: r^=x
                    y>>=1; x<<=1
                    if x&s.q: x^=s.P
                s.mt[a][b]=r
    def mul(s,a,b): return s.mt[a][b]
    def pow(s,a,e):
        r=1
        while e:
            if e&1: r=s.mt[r][a]
            a=s.mt[a][a]; e>>=1
        return r
    def inv(s,a): return s.pow(a,s.q-2)
    def tr(s,a):
        t=0;x=a
        for _ in range(s.m): t^=x; x=s.mt[x][x]
        return t
    def sqrt(s,a): return s.pow(a,s.q//2)
class Ring:
    """R_K = GR(2^K,m), elements as tuples of m ints mod 2^K."""
    def __init__(s,m,K):
        s.m=m; s.K=K; s.M=1<<K; s.FH=[(POLYS[m]>>i)&1 for i in range(m+1)]
        s.zero=(0,)*m; s.one=(1,)+(0,)*(m-1)
    def mul(s,a,b):
        m=s.m; c=[0]*(2*m-1)
        for i in range(m):
            if a[i]:
                for j in range(m): c[i+j]+=a[i]*b[j]
        for d in range(2*m-2,m-1,-1):
            t=c[d]
            if t:
                for i in range(m): c[d-m+i]-=t*s.FH[i]
            c[d]=0
        return tuple(x%s.M for x in c[:m])
    def add(s,a,b): return tuple((x+y)%s.M for x,y in zip(a,b))
    def sub(s,a,b): return tuple((x-y)%s.M for x,y in zip(a,b))
    def smul(s,c,a): return tuple((c*x)%s.M for x in a)
    def lift(s,x): return tuple((x>>i)&1 for i in range(s.m))
    def pw(s,x,e):
        r=s.one
        while e:
            if e&1: r=s.mul(r,x)
            x=s.mul(x,x); e>>=1
        return r
    def ev(s,terms,x):
        acc=s.zero
        for e,cd in terms:
            acc=s.add(acc,s.mul(tuple(v%s.M for v in cd),s.pw(x,e)))
        return acc
    def inv(s,a):  # unit inverse via Newton
        # residue inverse first
        F=Field(s.m); r=F.inv(res(a)); y=s.lift(r)
        for _ in range(s.K+1):
            y=s.mul(y,s.sub(s.smul(2,s.one),s.mul(a,y)))
        assert s.mul(a,y)==s.one
        return y
    def pack(s,a): return sum(v<<(s.K*i) for i,v in enumerate(a))
    def unpack(s,n): return tuple((n>>(s.K*i))&(s.M-1) for i in range(s.m))
    def val(s,a):
        v=s.K
        for x in a:
            if x:
                t=0
                while not (x>>t)&1: t+=1
                v=min(v,t)
        return v
def res(t): return sum((v&1)<<i for i,v in enumerate(t))
def div(t,d,M=None):
    assert all(v%d==0 for v in t),(t,d)
    return tuple(v//d for v in t)
def read_terms(fn,m):
    L=open(fn).read().split('\n'); n=int(L[0]); T=[]
    for l in L[1:1+n]:
        v=list(map(int,l.split())); T.append((v[0],v[1:1+m]))
    return T
def write_terms(fn,T):
    with open(fn,'w') as f:
        f.write(f"{len(T)}\n")
        for e,cd in T: f.write(f"{e} "+" ".join(str(c) for c in cd)+"\n")
def residue_coeffs(T,m):
    c={}
    for e,cd in T:
        c[e]=c.get(e,0)^sum((v&1)<<i for i,v in enumerate(cd))
    return {e:v for e,v in c.items() if v}
