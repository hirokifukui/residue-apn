# search F2-operators U, M (support in positions -R..R) with Tr(U(x)/M(x)) constant on {x: M(x)!=0}
import sys, itertools
sys.path.insert(0,'.')
from sym import GF
R=int(sys.argv[1]); ms=[5,7,9]
Fs={m:GF(m) for m in ms}
pos=list(range(-R,R+1))
def ev(F,S,x):
    s=0
    for p in S: s^=F.frob(x,p%F.m)
    return s
# precompute frob tables
tabs={}
for m,F in Fs.items():
    tabs[m]={p:[F.frob(x,p%m) for x in range(F.q)] for p in pos}
    F.invt=[0]+[F.inv(x) for x in range(1,F.q)]
    F.trt=[F.tr(x) for x in range(F.q)]
supports=[S for k in range(1,len(pos)+1) for S in itertools.combinations(pos,k)]
# normalize: M must have min position... allow all
res=[]
for M in supports:
    if len(M)>3: continue
    for U in supports:
        if len(U)>4: continue
        ok=True; kap=None
        for m,F in Fs.items():
            T=tabs[m]
            for x in range(1,F.q):
                mv=0
                for p in M: mv^=T[p][x]
                uv=0
                for p in U: uv^=T[p][x]
                if mv==0:
                    if uv==0: ok=False;break
                    continue
                t=F.trt[F.mul(uv,F.invt[mv])]
                if kap is None: kap=(m,t)
                k2=t
                if kap[0]!=m: kap=(m,t)
                if t!=kap[1]: ok=False;break
            if not ok: break
        if ok: res.append((U,M)); print('FOUND U',U,'M',M, flush=True)
print('done',len(res))
