import json, sys
from gen1 import *
from grlib import write_terms
# predicates return True when satisfied, else an int score (higher = closer)
def lv(log,L): return [x for x in log if x[0]==L and x[1] in ('res','nonres','D=2','D=1')]
def P(spec):
    def f(log):
        sc=0
        for L,want in enumerate(spec):
            e=lv(log,L)
            if not e: return sc
            e=e[0]
            if not want(e): return sc
            sc+=1
        return True
    return f
res_i1=lambda e: e[1]=='res' and e[5]==1
res_i0=lambda e: e[1]=='res' and e[5]==0
nonres=lambda e: e[1]=='nonres'
nonres_ia=lambda e: e[1]=='nonres' and e[5]==1
nonres_ib=lambda e: e[1]=='nonres' and e[6]==1
nonres_both=lambda e: e[1]=='nonres' and e[5]==1 and e[6]==1
anyl=lambda e: True
d2s=lambda s: (lambda e: e[1]=='D=2' and e[2]==s)
jobs=json.loads(sys.argv[1]); out=sys.argv[2]
for J in jobs:
    base,k,j,ub,seed,specname=J
    spec={'res_i1':[res_i1],'res_i0':[res_i0],'nonres_ia':[nonres_ia],'nonres_ib':[nonres_ib],'nonres_both':[nonres_both],
          'res_i1_res_i1':[res_i1,res_i1],'res_i1_nonres':[res_i1,nonres],'res_i1_res_i0':[res_i1,res_i0],
          'res_i1_d2q':[res_i1,d2s(32)],'res_i1_d2_1':[res_i1,d2s(1)],'res_i1_d2_2':[res_i1,d2s(2)],'nonres':[nonres]}[specname]
    r=search(base,k,j,ub,seed,P(spec))
    if r is None: print('FAILED',J,flush=True); continue
    T,C,a,log,M,alpha=r
    fn=f'lifts_r06/s1_{base}_k{k}j{j}u{ub}_s{seed}_{specname}.txt'; write_terms(fn,T)
    rec=dict(file=fn,k=k,j=j,ubar=ub,alpha=C.R.pack(alpha),a=a,spec=specname,log=log,pred=dict(nz(M)))
    open(out,'a').write(json.dumps(rec)+"\n"); print('OK',J,log,flush=True)
