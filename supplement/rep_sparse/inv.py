# Independent invariant computation (Claude r04): mu, rho, Lambda, Z, A_F, E_F, chi_F for a lift given as terms file.
import sys, json
POLYS={5:0b100101,7:0b10000011,9:0b1000010001,11:(1<<11)|0b101,13:(1<<13)|0b11011}
class Field:
    def __init__(s,m):
        s.m=m; s.q=1<<m; s.P=POLYS[m]
    def mul(s,a,b):
        r=0
        while b:
            if b&1: r^=a
            b>>=1; a<<=1
            if a&s.q: a^=s.P
        return r
    def pow(s,a,e):
        r=1
        while e:
            if e&1: r=s.mul(r,a)
            a=s.mul(a,a); e>>=1
        return r
    def inv(s,a): return s.pow(a,s.q-2)
    def tr(s,a):
        t=0;x=a
        for _ in range(s.m): t^=x; x=s.mul(x,x)
        assert t in (0,1); return t
class Ring:
    def __init__(s,m,M):
        s.m=m; s.M=M; s.FH=[(POLYS[m]>>i)&1 for i in range(m+1)]
    def mul(s,a,b):
        m=s.m; c=[0]*(2*m-1)
        for i in range(m):
            if a[i]:
                for j in range(m): c[i+j]+=a[i]*b[j]
        for d in range(2*m-2,m-1,-1):
            t=c[d]%s.M
            if t:
                for i in range(m): c[d-m+i]-=t*s.FH[i]
            c[d]=0
        return tuple(x%s.M for x in c[:m])
    def add(s,a,b): return tuple((x+y)%s.M for x,y in zip(a,b))
    def sub(s,a,b): return tuple((x-y)%s.M for x,y in zip(a,b))
    def lift(s,x): return tuple((x>>i)&1 for i in range(s.m))
    def ev(s,terms,x):
        acc=(0,)*s.m; cache={}
        for e,cd in terms:
            p=(1,)+(0,)*(s.m-1); b=x; ee=e
            while ee:
                if ee&1: p=s.mul(p,b)
                b=s.mul(b,b); ee>>=1
            acc=s.add(acc,s.mul(tuple(v%s.M for v in cd),p))
        return acc
def res(t): return sum((v&1)<<i for i,v in enumerate(t))
def div(t,d,M):
    assert all(v%d==0 for v in t),t
    return tuple((v//d)%(M//d) for v in t)
def read_terms(fn,m):
    L=open(fn).read().split('\n'); n=int(L[0]); T=[]
    for l in L[1:1+n]:
        v=list(map(int,l.split())); T.append((v[0],v[1:1+m]))
    return T
def invariants(T,m):
    K=Field(m); q=K.q; R8=Ring(m,8)
    # residue polynomial values and derivative
    p=[res(R8.ev(T,R8.lift(a))) for a in range(q)]
    dT=[(e-1,[e*c for c in cd]) for e,cd in T if e>0]
    dp=[res(R8.ev(dT,R8.lift(a))) for a in range(q)]
    assert len(set(p))==q
    assert 0 not in dp
    rho=[y for y in range(1,q) if dp[y]==dp[0]][0]
    # mu = [X^2](p(X+rho)+p(X)) via second Hasse derivative residue
    h2=[(e-2,[(e*(e-1)//2)*c for c in cd]) for e,cd in T if e>=2]
    mu=res(R8.ev(h2,R8.lift(rho)))^res(R8.ev(h2,R8.lift(0)))
    Lam=[p[a^rho]^p[a]^K.mul(rho,dp[a]) for a in range(q)]
    Z=[a for a in range(q) if Lam[a]==0]
    tau=R8.lift(rho); A=[];E={}
    Fv={}
    def F(x):
        if x not in Fv: Fv[x]=R8.ev(T,x)
        return Fv[x]
    for a in range(q):
        x=R8.lift(a); y=R8.add(x,tau)
        d=R8.sub(R8.ev(dT,y),R8.ev(dT,x)); A.append(res(div(d,2,8)))
    for a in Z:
        x=R8.lift(a); x1=R8.add(x,tau); x2=R8.add(x1,tau)
        S=R8.sub(R8.add(F(x2),F(x)),R8.add(F(x1),F(x1)))
        E[a]=res(div(S,4,8))
    chi={}
    for a in Z:
        if mu and A[a]:
            chi[a]=K.tr(K.mul(K.mul(mu,E[a]),K.inv(K.mul(A[a],A[a]))))
    return dict(rho=rho,mu=mu,Z=Z,A=A,E=E,chi=chi,Lam=Lam)
def predicted_spectrum(iv,m,k):
    q=1<<m; z=len(iv['Z']); A0=iv['A'].count(0)
    if A0: return None
    if iv['mu']==0: return {q:(q-z)*q**(k-2), 2*q:(z//2)*q**(k-2)}
    nu=sum(1 for a in iv['Z'] if iv['chi'][a]==0)
    d={2*q:(q-nu)*q**(k-2)//2}
    if nu: d[4*q]=nu*q**(k-2)//4
    return d
if __name__=="__main__":
    m=int(sys.argv[1]); T=read_terms(sys.argv[2],m); iv=invariants(T,m)
    K=Field(m)
    # E periodicity check: E(a+rho)+E(a) == rho*A + rho^2*mu
    per=all(iv['E'][a]^iv['E'][a^iv['rho']]==K.mul(iv['rho'],iv['A'][a])^K.mul(K.mul(iv['rho'],iv['rho']),iv['mu']) for a in iv['Z'])
    out=dict(rho=iv['rho'],mu=iv['mu'],Z=iv['Z'],A_zero=iv['A'].count(0),A_set=sorted(set(iv['A']))[:8],E=iv['E'],chi=iv['chi'],E_periodicity_identity=per)
    for k in (3,4,5): out[f'pred_k{k}']=predicted_spectrum(iv,m,k)
    print(json.dumps(out))
