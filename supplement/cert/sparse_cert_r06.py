# sparse_cert_r06.py (Claude, R06, written from scratch; imports no submitted code)
# Finite certificate used in the proof of Thm sparse:
#  (1) t^17+t^3+1 is irreducible over F2 (Rabin test);
#  (2) #{(z,w) in F_{2^17}^2 : Q(z,w)=0} = 125769, Q=(h(z)+h(w))/(z+w), h=Z^15+Z^14+Z^12+Z^8
#      (= sum_v N_v(N_v-1) off the diagonal, N_v = |h^{-1}(v)|, plus the diagonal point (0,0) where Q(z,z)=z^14);
#  (3) |C_m| = #{c in F_q \ F_2 : B_c injective}, B_c = X^(q/4)+X^(q/2)+X+X^2+cX^4, m = 5,...,13, by two methods
#      (complement of h(F_q^*), and the F2-rank of B_c). Requires python3 and numpy; runs in about one second.
import json, sys, numpy as np
def pmulmod(a,b,f,deg):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if a>>deg&1: a^=f
    return r
def irreducible(f,deg):
    # Rabin: x^(2^deg)=x mod f and gcd(x^(2^(deg/p))-x,f)=1 for every prime p | deg
    def ppow2(k):
        x=2
        for _ in range(k): x=pmulmod(x,x,f,deg)
        return x
    def pgcd(a,b):
        while b:
            while a and a.bit_length()>=b.bit_length(): a^=b<<(a.bit_length()-b.bit_length())
            a,b=b,a
        return a
    if ppow2(deg)!=2: return False
    ps=[p for p in range(2,deg+1) if deg%p==0 and all(p%d for d in range(2,p))]
    return all(pgcd(ppow2(deg//p)^2,f)==1 for p in ps)
def tables(f,deg):
    q=1<<deg; ex=np.zeros(2*q,dtype=np.int64); lg=np.full(q,-1,dtype=np.int64)
    fac=[p for p in range(2,q) if (q-1)%p==0 and all(p%d for d in range(2,int(p**.5)+1))]
    for g in range(2,q):           # a primitive element: order q-1
        ok=True
        for p in fac:
            e=(q-1)//p; x=1; b=g
            while e:
                if e&1: x=pmulmod(x,b,f,deg)
                b=pmulmod(b,b,f,deg); e>>=1
            if x==1: ok=False;break
        if ok: break
    x=1
    for i in range(q-1):
        ex[i]=x; lg[x]=i; x=pmulmod(x,g,f,deg)
    ex[q-1:2*q-2]=ex[:q-1]
    return ex,lg,q
def powvec(ex,lg,q,e):
    z=np.arange(q); out=np.zeros(q,dtype=np.int64); nz=z!=0
    out[nz]=ex[(lg[z[nz]]*e)%(q-1)]
    return out
def hvals(f,deg):
    ex,lg,q=tables(f,deg)
    return powvec(ex,lg,q,15)^powvec(ex,lg,q,14)^powvec(ex,lg,q,12)^powvec(ex,lg,q,8),ex,lg,q
res={}
f17=(1<<17)|(1<<3)|1
res['irreducible_t17_t3_1']=irreducible(f17,17)
h,_,_,q=hvals(f17,17)
cnt=np.bincount(h,minlength=q).astype(np.int64)
offdiag=int((cnt*(cnt-1)).sum())
res['F2^17_points']={'offdiagonal':offdiag,'diagonal':1,'total':offdiag+1}
fs={5:(1<<5)|(1<<2)|1,7:(1<<7)|2|1,9:(1<<9)|(1<<4)|1,11:(1<<11)|(1<<2)|1,13:(1<<13)|(1<<4)|(1<<3)|2|1}
res['Cm']={}
for m,f in fs.items():
    assert irreducible(f,m)
    hv,ex,lg,q=hvals(f,m)
    img=set(hv[1:].tolist())          # c with a nonzero kernel element
    meth1=sum(1 for c in range(2,q) if c not in img)
    def mul(a,b): return 0 if a==0 or b==0 else int(ex[lg[a]+lg[b]])
    def sq(a,k):
        for _ in range(k): a=mul(a,a)
        return a
    pre=[(sq(b,m-2)^sq(b,m-1)^b^sq(b,1), sq(b,2)) for b in [1<<i for i in range(m)]]
    def rank(cols):
        rows=list(cols); r=0
        for bit in range(m):
            piv=next((i for i in range(r,len(rows)) if rows[i]>>bit&1),None)
            if piv is None: continue
            rows[r],rows[piv]=rows[piv],rows[r]
            for i in range(len(rows)):
                if i!=r and rows[i]>>bit&1: rows[i]^=rows[r]
            r+=1
        return r
    meth2=sum(1 for c in range(2,q) if rank([a^mul(c,b4) for a,b4 in pre])==m)
    res['Cm'][m]={'image_complement':meth1,'rank':meth2}
print(json.dumps(res,indent=1))
expect={5:15,7:42,9:126,11:506,13:2496}
ok=res['irreducible_t17_t3_1'] and res['F2^17_points']['total']==125769 and \
   all(res['Cm'][m]['image_complement']==v and res['Cm'][m]['rank']==v for m,v in expect.items())
print('SPARSE_CERT OK' if ok else 'SPARSE_CERT FAIL')
sys.exit(0 if ok else 1)
