import sympy as sp
z,w=sp.symbols('z w')
h=lambda t: t**15+t**14+t**12+t**8
N=sp.Poly(h(z)+h(w), z, w, modulus=2); D=sp.Poly(z+w, z, w, modulus=2)
Q,R=sp.div(N,D); assert R.is_zero
print('deg',Q.total_degree())
f=sp.factor_list(Q.as_expr(), z, w, modulus=2)
for fac,e in f[1]: print(e, sp.Poly(fac,z,w,modulus=2).total_degree(), fac)
