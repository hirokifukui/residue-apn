# independent: build p_d = (Tr(x) + d x^{2^{m-2}})^3 by interpolation at DO/linear exponents, write inv.py term file
import sys
m=int(sys.argv[1]); POLY={13:8219,11:2053}[m]; q=1<<m
def mul(a,b):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if a&q: a^=POLY
    return r
def pw(a,e):
    r=1
    while e:
        if e&1: r=mul(r,a)
        a=mul(a,a); e>>=1
    return r
tr=lambda x: [x:=x] and (lambda s: s)(0)
def Tr(x):
    s=0; y=x
    for _ in range(m): s^=y; y=mul(y,y)
    return s
# pick smallest d with Tr d = Tr(1/d) = 0
d=next(d for d in range(2,q) if Tr(d)==0 and Tr(pw(d,q-2))==0)
f=[0]*q
for a in range(q):
    y=Tr(a)^mul(d,pw(a,1<<(m-2)))
    f[a]=mul(y,mul(y,y))
E=[1<<i for i in range(m)]+[(1<<i)+(1<<j) for i in range(m) for j in range(i+1,m)]
terms=[]
for e in E:
    c=0
    for a in range(1,q):
        if f[a]: c^=mul(f[a],pw(a,q-1-e))
    if c: terms.append((e,c))
# sanity: re-evaluate
for a in range(0,q,97):
    v=0
    for e,c in terms: v^=mul(c,pw(a,e))
    assert v==f[a],a
with open(f'p{m}_d{d}.txt','w') as fh:
    fh.write(f"{len(terms)}\n")
    for e,c in terms: fh.write(f"{e} "+" ".join(str((c>>i)&1) for i in range(m))+"\n")
print(m,d,len(terms), 'rho_expected', pw(pw(d,q-2),4))
