import sympy as sp
exec(open('symcomp.py').read().split("u=U**")[0])
K=4
a1=U**(2**K); a2=V**(2**K); a3=W**(2**K); t1=T1**(2**K); t2=T2**(2**K)
A=comp(S(a1),comp(sc(t1),comp(S(a2),comp(sc(t2),S(a3)))))
def pretty(p):
    # convert exponents back: each var exponent / 16
    out=[]
    for mon,c in p.terms():
        out.append('*'.join('%s^%s'%(n,sp.Rational(e,16)) for n,e in zip(['a1','th1','th2','a2','a3'],mon) if e))
    return ' + '.join(out) if out else '0'
for k in sorted(A): print(k,':',pretty(A[k]))
