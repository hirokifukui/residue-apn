# R05-01 (Claude): normalization of the multi-word transition probability (paper Prop. markov; GPT R04b M1).
# P_S(a->b) = prod_j [delta_F(a_j,b_j)/q^k] = q^{-kn} prod_j delta_F(a_j,b_j).
# Part A (n = 2, GR(8,5), S = P53sp wordwise): a = b = (1,0) has probability 64*32768/32768^2 = 1/512.
#   The misreading "prod_j delta / q^k" (one division) would give 64, which is not a probability.
# Part B (exhaustive Markov check, n = 2 words over Z/8, two rounds): S a random permutation of Z/8 applied
#   wordwise, M = [[1,1],[1,2]] (invertible mod 8). For every characteristic (D0 != 0, D1, D2) the exact probability
#   over uniform (X0, kappa1) equals P_S(D0 -> M^{-1} D1) * P_S(D1 -> M^{-1} D2) with the per-word normalization.
import os, sys, json, random, itertools
here=os.path.dirname(os.path.abspath(__file__)); root=os.path.dirname(here); sys.path.insert(0, root); os.chdir(root)
from inv import Ring, read_terms
from fractions import Fraction as Fr
out={}
# ---- Part A
m=5; R=Ring(m,8); T=read_terms('P53sp.txt',m)
N=8**m
els=[tuple((i>>(3*j))&7 for j in range(m)) for i in range(N)]
val={x:R.ev(T,x) for x in els}
one=(1,0,0,0,0); zero=(0,)*m
def delta(a,b):
    return sum(1 for x in els if R.sub(val[R.add(x,a)],val[x])==b)
d11=delta(one,one); d00=delta(zero,zero)
pA=Fr(d11*d00, N**2); mis=Fr(d11*d00, N)
out['partA']=dict(delta_1_1=d11, delta_0_0=d00, P=str(pA), misreading=str(mis))
assert d11==64 and d00==N and pA==Fr(1,512) and mis>1, out['partA']
# ---- Part B
random.seed(20261025)
Q=8; perm=list(range(Q)); random.shuffle(perm)
def S(v): return tuple(perm[t] for t in v)
M=((1,1),(1,2))
def Mv(v): return tuple((M[i][0]*v[0]+M[i][1]*v[1])%Q for i in range(2))
Minv=((2,-1),(-1,1))   # det = 1
def Minvv(v): return tuple((Minv[i][0]*v[0]+Minv[i][1]*v[1])%Q for i in range(2))
assert all(Minvv(Mv(v))==v for v in itertools.product(range(Q),repeat=2))
dd=[[sum(1 for x in range(Q) if (perm[(x+a)%Q]-perm[x])%Q==b) for b in range(Q)] for a in range(Q)]
def PS(a,b):  # per-word normalization
    p=Fr(1)
    for aj,bj in zip(a,b): p*=Fr(dd[aj][bj],Q)
    return p
V=list(itertools.product(range(Q),repeat=2))
add=lambda u,v: tuple((s+t)%Q for s,t in zip(u,v)); sub=lambda u,v: tuple((s-t)%Q for s,t in zip(u,v))
cnt={}
for D0 in V:
    if D0==(0,0): continue
    for x0 in V:
        D1=Mv(sub(S(add(x0,D0)),S(x0)))
        for k1 in V:
            x1=add(Mv(S(x0)),k1)
            D2=Mv(sub(S(add(x1,D1)),S(x1)))
            cnt[(D0,D1,D2)]=cnt.get((D0,D1,D2),0)+1
nchar=0; bad=0
for D0 in V:
    if D0==(0,0): continue
    for D1 in V:
        for D2 in V:
            nchar+=1
            exact=Fr(cnt.get((D0,D1,D2),0), len(V)**2)
            if exact!=PS(D0,Minvv(D1))*PS(D1,Minvv(D2)): bad+=1
out['partB']=dict(words=2, ring='Z/8', characteristics=nchar, mismatches=bad)
assert bad==0
json.dump(out, open('tests/markov_two_words.json','w'), indent=1)
print(json.dumps(out)); print('MARKOV_TWO_WORDS OK')
