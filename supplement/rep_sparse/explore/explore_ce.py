# 4-term A = x + e^-2 x^2 + c x^(2^(m-2)) + e x^(2^(m-1)), p = A^3 ; mu=0 automatically.
import sys
sys.path.insert(0, '.')
from sym import *
from collections import Counter
m = int(sys.argv[1]); F = GF(m)
mode = sys.argv[2] if len(sys.argv)>2 else 'all'
cnt = Counter(); good=[]
def Aco(c,e): return {0:1, 1:F.inv(F.sq(e)), m-2:c, m-1:e}
pairs=[]
if mode=='all':
    pairs=[(c,e) for c in range(1,F.q) for e in range(1,F.q)]
elif mode=='c1': pairs=[(1,e) for e in range(1,F.q)]
elif mode=='e1': pairs=[(c,1) for c in range(1,F.q)]
elif mode=='ce': pairs=[(e,e) for e in range(1,F.q)]
for c,e in pairs:
    A=Aco(c,e)
    if not lin_invertible(F,A): cnt['noninv']+=1; continue
    iv=invariants(F,*expand_LA3(F,A,{0:1}))
    if not iv['H']: cnt['noH']+=1; continue
    assert iv['mu']==0
    cnt[('z',iv['z'])]+=1
    if iv['z']==0: good.append((c,e))
print(m, mode, dict(cnt), good[:8])
