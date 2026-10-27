# R03-03: dimension-free algebraic certificates (Claude). No enumeration over m.
# Conventions (m>=5 odd, q=2^m): u=2^(m-2), v=2^(m-1), Y=X^(u/2), U=X^u=Y^2, V=X^v=U^2.
# Exact congruences used (every m>=5, integer polynomials mod 4):
#   (X+1)^(2^j) == X^(2^j) + 1 + 2 X^(2^(j-1)) (mod 4), j>=1  [base + inductive step checked below]
#   hence (X+1)^u == U+1+2Y, (X+1)^v == V+1+2U (mod 4); 4 | u, 4 | v.
# Relation used only on F_q (after reduction mod 2): V^2 = X.
from sympy import symbols, expand, Poly, ZZ
X,Y,U,V,t,P,W,Wh = symbols('X Y U V t P W Wh')
G=(X,Y,U,V,t,P,W,Wh)
def mod(e,n):
    p=Poly(expand(e),*G,domain=ZZ)
    return Poly({k:(c%n) for k,c in p.terms()},*G,domain=ZZ).as_expr()
def halfmod2(e):
    p=Poly(expand(e),*G,domain=ZZ); assert all(c%2==0 for c in p.coeffs())
    return Poly({k:((c//2)%2) for k,c in p.terms()},*G,domain=ZZ).as_expr()
def redU(e):  # exact relation U^2 = V (X^(2u) = X^v), used before reduction mod 2
    p=Poly(expand(e),*G,domain=ZZ); out={}
    iU=G.index(U); iV=G.index(V)
    for k,c in p.terms():
        k=list(k); k[iV]+=k[iU]//2; k[iU]%=2; k=tuple(k); out[k]=out.get(k,0)+c
    return Poly(out,*G,domain=ZZ).as_expr()
def zero2(e): return mod(redU(e),2)==0
ok={}
ok['binom_base']= mod((X+1)**2-(X**2+1+2*X),4)==0
ok['binom_step']= mod((P**2+1+2*P)**2 - (P**4+1+2*P**2),4)==0
# r=3 natural lift
F  = X+X**2+X**3+X*U+X**2*U+X**2*V+U*V
Us, Vs = U+1+2*Y, V+1+2*U
Fs = (X+1)+(X+1)**2+(X+1)**3+(X+1)*Us+(X+1)**2*Us+(X+1)**2*Vs+Us*Vs
Fd = 1+2*X+3*X**2+U+2*X*U+2*X*V
half = halfmod2(mod(Fs-F-Fd,4)); ok['num_even']=True
ok['half_matches']= zero2(half-(1+X**2+U+Y+X*Y+X**2*Y+X**2*U+Y*V))
Enat = mod(half+(1+X+U+V),2)
ok['Enat'] = zero2(Enat-(X+X**2+Y+X*Y+X**2*Y+X**2*U+V+Y*V))
ok['Enat_at_0'] = Enat.subs({X:0,Y:0,U:0,V:0})%2==0
Fds = 1+2*(X+1)+3*(X+1)**2+Us+2*(X+1)*Us+2*(X+1)*Vs
ok['A_r3'] = zero2(halfmod2(mod(Fds-Fd,4))-(1+X+Y+U+V))
ok['Dj'] = zero2((X+1)**2*(U+1)-X**2*U-(X**2+U+1))
Enew = mod(Enat + X**4+V+1,2)
sub={Y:t,U:t**2,V:t**4,X:t**8}
A  = (1+X+Y+U+V).subs(sub); phi=(1+X**2+X*V+Y*V+U*V).subs(sub)
ok['phi_identity'] = zero2(phi**2+A*phi-(Enew+(1+X+Y+U+V)**2).subs(sub))
# r>=5: F' mod 4 = 1+2X+W+2XW+U+2XU, W=X^w (w=2^(r-2)>=8), Wh=X^(w/2)
Fd5 = 1+2*X+W+2*X*W+U+2*X*U
Fd5s= 1+2*(X+1)+(W+1+2*Wh)+2*(X+1)*(W+1+2*Wh)+(U+1+2*Y)+2*(X+1)*(U+1+2*Y)
ok['A_r5'] = zero2(halfmod2(mod(Fd5s-Fd5,4))-(Wh+W+Y+U))
# correction 2X^3: h = residue of (X^3)' = X^2 ; D_1 h = 1
ok['corr_r5'] = zero2((X+1)**2+X**2-1)
for k,v in ok.items(): print(f"{k:16s} {v}")
assert all(ok.values()); print("IDENTITIES_CERT OK")
