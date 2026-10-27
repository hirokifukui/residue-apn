# symbolic composition of sigma-polynomials over F_2(params); params stored as 2^K-th powers so sqrt is exact
import sympy as sp
K=4
U,T1,T2,V,W=sp.symbols('U T1 T2 V W')
gens=(U,T1,T2,V,W)
def P(e): return sp.Poly(e, *gens, modulus=2)
def frob(p,k):
    # p^(2^k) for k>=0 ; for k<0 halve exponents (must be divisible)
    d={}
    for mon,c in p.terms():
        if k>=0: nm=tuple(e*(2**k) for e in mon)
        else:
            f=2**(-k)
            assert all(e%f==0 for e in mon), (mon,k)
            nm=tuple(e//f for e in mon)
        d[nm]=(d.get(nm,0)+c)%2
    return sp.Poly.from_dict({k:v for k,v in d.items() if v}, *gens, modulus=2) if any(d.values()) else P(0)
def comp(B,C):
    R={}
    for i,b in B.items():
        for j,c in C.items():
            R[i+j]=R.get(i+j,P(0))+b*frob(c,i)
    return {k:v for k,v in R.items() if not v.is_zero}
def S(x): return {-1:P(x),0:P(1),1:P(1)}
def sc(x): return {0:P(x)}
u=U**(2**K); t1=T1**(2**K); t2=T2**(2**K)
A=comp(S(u),comp(sc(t1),comp(S(u),comp(sc(t2),S(u)))))
for k in sorted(A): print(k, A[k].as_expr())
