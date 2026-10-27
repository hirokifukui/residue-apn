# R04-03 (Claude): probability model of the cryptographic product bound (CRYPTOGRAPHIC_COROLLARY_v2.md, Prop. C3').
# Part 1 (the reviewer's counterexample, recomputed): GR(8,5), S = P53sp, one word, M = 1, two rounds
#   x -> S(x) + kappa_i with independent uniform round keys, FIXED plaintext pair (0, 1).
#   The first-round difference S(1) - S(0) is deterministic, so the key-averaged probability of 1 -> 1 -> 1 is
#   1 * delta(1,1)/|R|, which exceeds the product (delta(1,1)/|R|)^2.  The fixed-plaintext model is not Markov.
# Part 2 (the corrected model, exhaustive on a toy ring): GR(8,3) additive group, S a random permutation table.
#   With X0 uniform and independent of the round keys, for EVERY characteristic (D0 != 0, D1, D2) the exact
#   probability equals DDT(D0,D1) DDT(D1,D2) / |R|^2 (brute force over all |R|^2 pairs (X0, kappa1)).
#   With X0 = 0 fixed, some characteristic exceeds (max DDT / |R|)^2.
import os, sys, json, random
import numpy as np
here=os.path.dirname(os.path.abspath(__file__)); root=os.path.dirname(here); sys.path.insert(0, root); os.chdir(root)
from inv import Ring, read_terms
from fractions import Fraction as Fr
out={}
# ---- Part 1
m=5; R=Ring(m,8); T=read_terms('P53sp.txt',m)
els=[tuple((i>>(3*j))&7 for j in range(m)) for i in range(8**m)]
val={x:R.ev(T,x) for x in els}
one=(1,0,0,0,0); zero=(0,)*m; N=8**m
d01=R.sub(val[one],val[zero])
delta11=sum(1 for x in els if R.sub(val[R.add(x,one)],val[x])==one)
p_fixed=Fr(1 if d01==one else 0)*Fr(delta11,N); p_prod=Fr(delta11,N)**2
out['part1']=dict(ring='GR(8,5)',S='P53sp',F0=list(val[zero]),F1=list(val[one]),first_round_difference=list(d01),
    delta_1_1=delta11,R=N,p_fixed_plaintext=str(p_fixed),product_bound=str(p_prod),violates=p_fixed>p_prod)
print(json.dumps(out['part1']))
ok1 = (d01==one and delta11==64 and p_fixed==Fr(1,512) and p_prod==Fr(1,262144))
# ---- Part 2
m2=3; n=8**m2; rng=random.Random(20261025); perm=list(range(n)); rng.shuffle(perm); S=np.array(perm)
def add(a,b):  # GR(8,3) addition on packed 3-bit digits
    return ((((a&0o7)+(b&0o7))&7) | ((((a>>3)&7)+((b>>3)&7))&7)<<3 | ((((a>>6)&7)+((b>>6)&7))&7)<<6)
def neg(a): return ((-(a&7))&7) | ((-((a>>3)&7))&7)<<3 | ((-((a>>6)&7))&7)<<6
A=np.arange(n); ADD=np.array([[add(a,b) for b in range(n)] for a in range(n)]); NEG=np.array([neg(a) for a in range(n)])
SUB=lambda a,b: ADD[a,NEG[b]]
DDT=np.zeros((n,n),dtype=np.int64)
for d in range(n):
    np.add.at(DDT[d], SUB(S[ADD[A,d]],S[A]), 1)
maxddt=DDT[1:].max()
worst_ratio_uniform=Fr(0); mism=0; worst_fixed=Fr(0)
for d0 in range(1,n):
    x0=A; d1=SUB(S[ADD[x0,d0]],S[x0])                  # (n,)
    y1=ADD[S[x0][:,None],A[None,:]]                     # (n,n): y1 = S(x0) + kappa1
    d2=SUB(S[ADD[y1,d1[:,None]]],S[y1])                 # (n,n)
    C=np.zeros((n,n),dtype=np.int64); np.add.at(C,(np.broadcast_to(d1[:,None],(n,n)),d2),1)
    pred=np.outer(DDT[d0],np.ones(n,dtype=np.int64))*DDT          # DDT(d0,d1)*DDT(d1,d2)
    mism+=int((C!=pred).sum())                                     # exact: C/n^2 == pred/n^2
    # fixed plaintext X0 = 0
    f1=int(SUB(S[add(0,d0)],S[0])); row=DDT[f1]                    # P_fixed(d0,f1,d2) = row[d2]/n
    worst_fixed=max(worst_fixed,Fr(int(row.max()),n)/Fr(int(maxddt),n)**2)
out['part2']=dict(ring='GR(8,3) (additive group), random permutation S, seed 20261025',R=n,max_DDT=int(maxddt),
    characteristics_checked=(n-1)*n*n,uniform_start_mismatches=mism,
    fixed_plaintext_max_ratio_to_product_bound=str(worst_fixed),fixed_plaintext_violates=worst_fixed>1)
print(json.dumps(out['part2']))
ok2 = (mism==0 and worst_fixed>1)
json.dump(out,open(os.path.join(here,'crypto_c3_test.json'),'w'),indent=1)
if not (ok1 and ok2): print('CRYPTO_C3_TEST FAIL'); sys.exit(1)
print('CRYPTO_C3_TEST OK')
