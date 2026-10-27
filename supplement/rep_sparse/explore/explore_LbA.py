# p = L(beta * A^3), L, A in F2[sigma] (support subsets of -2..2), beta in F_q
import sys, itertools
sys.path.insert(0,'.')
from sym import *
pos=[-2,-1,0,1,2]
sups=[S for k in range(2,6) for S in itertools.combinations(pos,k)]
def run(m, pairs=None):
    F=GF(m); out={}
    for SL in sups:
        for SA in sups:
            if pairs is not None and (SL,SA) not in pairs: continue
            A={p%m:1 for p in SA}
            Lb={p%m:1 for p in SL}
            if len(A)<len(SA) or len(Lb)<len(SL): continue
            if not (lin_invertible(F,A) and lin_invertible(F,Lb)): continue
            good=0; tot=0
            for b in range(2,F.q):
                L={k:F.frob(b,k) for k in Lb}
                c,l=expand_LA3(F,A,L)
                iv=invariants(F,c,l)
                tot+=1
                if iv['H'] and iv['mu']==0 and iv['z']==0: good+=1
            if good: out[(SL,SA)]=(good,tot)
    return out
o5=run(5); print('m5',len(o5), flush=True)
o7=run(7,set(o5)); print('m7',len(o7), flush=True)
for k,v in o7.items(): print(k, o5[k], v)
print('m5 list', o5)
o7=run(7); print('m7 all', o7, flush=True)
