# Theory predictor for rows alpha in v_j (1<=j<=k-3) of a lift F of p satisfying (H).
# Computes the local invariants of the row from a handful of evaluations of F and assembles the
# predicted spectrum from the class/pair formulas of RESULT.md (Theorems L1-L4). Returns None-flags where
# the theorem makes no prediction.
import sys, json
from collections import Counter
from grlib import *
from pinv import pinv, peval

def S_nd(c3nz,d):            # class multiset (values N, incl. zeros) of a nondegenerate class, depth d>=0, over q^d targets
    q=Q
    if d==0: return Counter({1:1})
    return Counter({2:q**d//2,0:q**d//2}) if c3nz else Counter({1:q**d})
_memo={}
_Acache={}
def S_deg(d):                # universal degenerate tree (w=0, c!=0), incl. zeros
    q=Q
    if (q,d) in _memo: return _memo[(q,d)]
    if d==0: r=Counter({1:1})
    elif d==1: r=Counter({1:q})
    else:
        r=Counter()
        for v,c in S_deg(d-2).items(): r[q*v]+=c
        for v,c in S_nd(True,d-2).items(): r[q*v]+=(q-1)*c
        r[0]+=q**d-q**(d-1)   # unmatched second digit
    _memo[(q,d)]=r; return r
def S_deg_closed(d):         # closed form (nonzero part) -- Theorem L2
    q=Q; r=Counter()
    for i in range(1,(d-1)//2+1): r[2*q**i]+=(q-1)*q**(d-2*i)//2
    r[q**(d//2)]+=q
    return r
def nz(c): return Counter({v:x for v,x in c.items() if v and x})

class Row:
    def __init__(s,T,m,k,alpha,Fd,pdat):
        s.m=m;s.k=k;s.F=Fd;s.q=Fd.q;s.T=T
        s.R=Ring(m,k); s.alpha=alpha
        j=s.R.val(alpha); s.j=j; s.n=k-j; s.d=s.n-2
        s.Rn=Ring(m,s.n)
        u=tuple((v>>j) for v in alpha)   # alpha = 2^j * u  (u determined mod 2^{k-j})
        s.ubar=res(u)
        s.uinv=s.Rn.inv(tuple(v%(1<<s.n) for v in u))
        s.p=pdat; s.cache={}
    def Fv(s,x):
        if x not in s.cache: s.cache[x]=s.R.ev(s.T,x)
        return s.cache[x]
    def Tv(s,x):   # T(x) = (F(x+alpha)-F(x))/alpha in R_n
        D=s.R.sub(s.Fv(s.R.add(x,s.alpha)),s.Fv(x))
        D=tuple(v%(1<<s.n) for v in div(D,1<<s.j))
        return s.Rn.mul(D,s.uinv)

def predict(T,m,k,alpha):
    global Q
    Fd=Field(m); q=Fd.q; Q=q
    c=residue_coeffs(T,m); P=pinv(c,m)
    row=Row(T,m,k,alpha,Fd,P); R=row.R; Rn=row.Rn; j=row.j; n=row.n; d=row.d
    assert 1<=j<=k-3
    rho=P['rho']; mu=P['mu']; c3=P['c3']; pi=P['pi']; ub=row.ubar
    tau=R.lift(rho); t=R.lift(2)   # t = the generator t (field element 2)
    two=lambda x: R.smul(2,x)
    info=dict(j=j,n=n,ubar=ub,rho=rho,mu=mu,c3=c3,checks=[])
    # residue of (Tv(x)-Tv(x0))/4^? helper
    def r4(a_,b_,sh):   # residue of (a_-b_)/2^sh in R_n
        D=Rn.sub(a_,b_); assert all(v%(1<<sh)==0 for v in D),(D,sh); return res(tuple(v>>sh for v in D))
    xs={a:R.lift(a) for a in range(q)}
    Tx={a:row.Tv(xs[a]) for a in range(q)}
    # class data: psi_a(y)=w y + c y^2 from y=1 and y=t
    cls={}
    for a in range(q):
        p1=r4(row.Tv(R.add(xs[a],two(R.one))),Tx[a],2)
        pt=r4(row.Tv(R.add(xs[a],two(R.lift(2)))),Tx[a],2)
        # pt + t*p1 = c (t^2+t)
        cc=Fd.mul(pt^Fd.mul(2,p1),Fd.inv(Fd.mul(2,2)^2)); w=p1^cc
        cls[a]=dict(w=w,c=cc)
        wpred=pi[a]^(Fd.mul(ub,c3) if j==1 else 0)
        if cc!=c3 or w!=wpred: info['checks'].append(('Lemma C fails',a,w,cc,wpred))
    # pairs
    B={}
    for a in range(q):
        B[a]=r4(row.Tv(R.add(xs[a],tau)),Tx[a],1)
    # check B = A_F + [j=1] ubar*mu via A_F computed from F'
    key=tuple((e,tuple(cd)) for e,cd in T)
    if key not in _Acache:
        dT=[(e-1,[e*x for x in cd]) for e,cd in T if e>0]
        R8=Ring(m,3); AA=[]
        for a in range(q):
            x=R8.lift(a); y=R8.add(x,R8.lift(rho))
            AA.append(res(div(R8.sub(R8.ev(dT,y),R8.ev(dT,x)),2)))
        _Acache[key]=AA
    AA=_Acache[key]
    for a in range(q):
        if B[a]!=AA[a]^(Fd.mul(ub,mu) if j==1 else 0): info['checks'].append(('Lemma B fails',a))
    total=Counter(); unpred=[]; ptypes=Counter()
    types={}
    def classtype(a):
        w=cls[a]['w']
        if w: return 'ND'
        if c3: return 'DEG'
        return 'DEEP'
    def class_multiset(a,dd):
        ty=classtype(a)
        if ty=='ND': return S_nd(c3!=0,dd)
        if ty=='DEG': return S_deg(dd)
        # DEEP: Phi = 2*Phit; read w',c' from (T(x+2y)-T(x))/8
        if dd==1: return Counter({q:1, 0:q-1})
        p1=r4(row.Tv(R.add(xs[a],two(R.one))),Tx[a],3)
        pt=r4(row.Tv(R.add(xs[a],two(R.lift(2)))),Tx[a],3)
        cc=Fd.mul(pt^Fd.mul(2,p1),Fd.inv(Fd.mul(2,2)^2)); w=p1^cc
        types[a]=('DEEP',w,cc); ptypes[('DEEPsub','w1!=0' if w else ('c1!=0' if cc else 'w1=c1=0'))]+=1
        if w:
            base=S_nd(cc!=0,dd-1)
        elif cc:
            base=S_deg(dd-1)
        else: return None
        r=Counter()
        for v,x in base.items(): r[q*v]+=x
        r[0]+=q**dd-q**(dd-1)
        return r
    done=set()
    for a in range(q):
        if a in done: continue
        b=a^rho; done|={a,b}
        if B[a]:   # unmerged
            for x in (a,b):
                ptypes[('U',classtype(x)+('' if classtype(x)!='ND' else ('c3=0' if c3==0 else 'c3!=0')))]+=1
                ms=class_multiset(x,d)
                if ms is None: unpred.append(('deep2',x)); continue
                for v,cnt in ms.items():
                    if v: total[v*q**(j+1)]+=cnt
            continue
        ta,tb=classtype(a),classtype(b)
        ptypes[('M','+'.join(sorted((ta,tb)))+('|mu=0' if mu==0 else '|mu!=0')+('|c3=0' if c3==0 else '')+('|d=1' if d==1 else ('|d=2' if d==2 else '|d>=3')))]+=1
        if d==1:
            # residue-level: N_x(gbar) for each class, sum with offset ebar (Lemma P, d=1)
            e=r4(Tx[a],Tx[b],2)
            def N1(x,gb):
                ty=classtype(x)
                if ty=='ND':
                    w=cls[x]['w']; return sum(1 for y in range(q) if Fd.mul(w,y)^Fd.mul(c3,Fd.mul(y,y))==gb)
                if ty=='DEG': return 1
                return q if gb==0 else 0
            ms=Counter()
            for g in range(q): ms[N1(a,g)+N1(b,g^e)]+=1
        elif c3==0 and (ta=='ND' or tb=='ND'):
            if ta!='ND': a,b=b,a
            other=class_multiset(b,d)
            if other is None: unpred.append(('deep2-merged',b)); continue
            ms=Counter()
            for v,x in other.items(): ms[v+1]+=x
        elif ta=='ND' and tb=='ND':
            if c3==0: ms=Counter({2:q**d})
            elif mu: ms=Counter({4:q**d//4,2:q**d//2})
            else:
                e=r4(row.Tv(R.add(xs[a],tau)),Tx[a],2)
                chi=Fd.tr(Fd.mul(Fd.mul(c3,e),Fd.inv(Fd.mul(cls[a]['w'],cls[a]['w']))))
                ms=Counter({4:q**d//2}) if chi==0 else Counter({2:q**d})
        elif c3 and mu and 'DEG' in (ta,tb):
            if ta!='DEG': a,b=b,a
            # degenerate class a, nondegenerate b (w_b = mu)
            e=r4(Tx[a],Tx[b],2)          # g_b = g_a + e (residues)
            wb=cls[b]['w']; Hb={Fd.mul(wb,y)^Fd.mul(c3,Fd.mul(y,y)) for y in range(q)}
            h=lambda gbar: 1 if (gbar^e) in Hb else 0
            if d==1:
                ms=Counter()
                for g in range(q): ms[1+2*h(g)]+=1
            else:
                # find degenerate child ybar*: child linear coefficient (Phi'(y)/2)bar = (W/2)bar + c3*y
                kappa=None
                if d>=3:
                    ystar=None
                    for y in range(q):
                        yh=R.lift(y); base=R.add(xs[a],two(yh))
                        T0=row.Tv(base)
                        q1=r4(row.Tv(R.add(base,R.smul(4,R.one))),T0,4)
                        qt=r4(row.Tv(R.add(base,R.smul(4,R.lift(2)))),T0,4)
                        cc=Fd.mul(qt^Fd.mul(2,q1),Fd.inv(Fd.mul(2,2)^2)); w1=q1^cc
                        if cc!=c3: info['checks'].append(('child c3 mismatch',a,y))
                        if w1==0: ystar=y if ystar is None else 'multi'
                    assert ystar is not None and ystar!='multi',ystar
                    gstar=Fd.mul(c3,Fd.mul(ystar,ystar))
                    kappa=h(gstar); info.setdefault('kappa',{})[a]=kappa
                    gs=gstar
                else: gs=None
                ms=Counter()
                for g in range(q):
                    hh=2*h(g)
                    ms[hh]+=q**(d-1)-q**(d-2)
                    child=S_deg(d-2) if (d>=3 and g==gs) else S_nd(True,d-2)
                    for v,x in child.items(): ms[q*v+hh]+=x
        elif ta=='DEG' and tb=='DEG' and d==2:
            # Proposition DD2: s = #{y: sigma_a(y)+sigma_b(y+y_e)+sqrt(c3*ebar)*y+e1 = 0}
            def teich(Rg,y): return Rg.pw(Rg.lift(y),Fd.q**(Rg.K-1))
            Rd=Ring(m,d)
            def sigma(x,y):
                Ty=teich(R,y); Ph=Rn.sub(row.Tv(R.add(xs[x] if x==a else R.add(xs[a],tau),two(Ty))),Tx[a] if x==a else row.Tv(R.add(xs[a],tau)))
                Ph=tuple(v%4 for v in div(Ph,4))  # in R_{n-2}=R_2
                t=teich(Rd,Fd.mul(c3,Fd.mul(y,y)))
                D=Rd.sub(Ph,t); return res(div(D,2))
            Txb=row.Tv(R.add(xs[a],tau))
            E=tuple(v%4 for v in div(Rn.sub(Tx[a],Txb),4)); eb=res(E)
            e1=res(div(Rd.sub(E,teich(Rd,eb)),2))
            ye=Fd.sqrt(Fd.mul(eb,Fd.inv(c3))); rce=Fd.sqrt(Fd.mul(c3,eb))
            sa=[sigma(a,y) for y in range(q)]; sb=[sigma(b,y) for y in range(q)]
            scount=sum(1 for y in range(q) if sa[y]^sb[y^ye]^Fd.mul(rce,y)^e1==0)
            info.setdefault('DD2_s',[]).append(scount)
            ms=nz(Counter({2*q:scount,q:2*(q-scount)}))
        else:
            unpred.append(('merged',a,ta,tb)); continue
        for v,cnt in ms.items():
            if v: total[v*q**(j+1)]+=cnt
    info['ptypes']={'/'.join(k):v for k,v in ptypes.items()}
    info['B_zero']=sum(1 for a in range(q) if B[a]==0)
    info['w_zero']=[a for a in range(q) if cls[a]['w']==0]
    if types: info['deep']=types
    return total,unpred,info

if __name__=="__main__":
    m=int(sys.argv[1]);k=int(sys.argv[2]);T=read_terms(sys.argv[3],m)
    R=Ring(m,k)
    for al in sys.argv[4:]:
        tot,un,info=predict(T,m,k,R.unpack(int(al)))
        print(al,dict(sorted(tot.items())),un,info)
