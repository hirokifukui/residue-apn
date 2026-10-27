# R04-01 regression (Claude): optimality at level 8 does NOT lift unconditionally.
# For each input the SAME integer coefficients are evaluated in GR(8,5) and GR(16,5) (compatible lifts).
# Expected (CROSS_LEVEL.md, Theorem CL): a level-8 minimizer stays optimal at k=4 iff A_F has no zero.
#   c1_o3          : mu!=0, Z empty, A==0  -> optimal at k=3 (q=32), NOT optimal at k=4 (rows reach q^2=1024; optimum 2q=64)
#   F1_c0A1_plus2X2: mu!=0, Z nonempty, A zero-free, chi==1 -> optimal at k=3 and k=4 (2q=64)
#   rep5_A1        : mu=0, Z empty, A zero-free -> optimal at k=3 and k=4 (q=32)
# Exit 0 iff every expectation holds. Uses the C row checker grddt3 (k=3: all 1024 exceptional rows; k=4: 4 sampled rows).
import subprocess, json, os, sys
here=os.path.dirname(os.path.abspath(__file__)); root=os.path.dirname(here); os.chdir(root)
sys.path.insert(0, root)
from inv import read_terms, invariants
m=5; q=32; GR='./grddt3'
def rows(fn,k,mode,rho):
    env=os.environ.copy(); env['RHO']=str(rho)
    p=subprocess.run([GR,str(m),str(k),'37',fn,'4','7',mode],capture_output=True,text=True,env=env,timeout=1800)
    if p.returncode!=0: raise SystemExit(f'checker exit {p.returncode}')
    L=p.stdout.splitlines()
    if not L or L[0]!='perm_dups 0': raise SystemExit('not a permutation / malformed')
    out=[]
    for ln in L[1:]:
        h,t=ln.split('|'); hd=h.split()
        if hd[0]=='exc': out.append({int(v):int(c) for v,c in (x.split('x') for x in t.split())})
    return out
cases=[('c1_o3.txt',dict(k3=q,k4_opt=False)),('F1_c0A1_plus2X2.txt',dict(k3=2*q,k4_opt=True)),('rep5_A1.txt',dict(k3=q,k4_opt=True))]
res=[]; bad=0
for fn,exp in cases:
    iv=invariants(read_terms(fn,m),m); A0=iv['A'].count(0); z=len(iv['Z']); mu=iv['mu']
    opt4 = q if (mu==0 and z==0) else 2*q          # minimax value at k>=4 (Theorem B)
    r3=rows(fn,3,'exc',iv['rho']); r4=rows(fn,4,'sample',iv['rho'])
    max3=max(max(h) for h in r3); max4=max(max(h) for h in r4)
    ok3 = (len(r3)==q*q and max3==exp['k3'])
    ok4 = (max4==opt4) if exp['k4_opt'] else (min(max(h) for h in r4)>=q*q)
    okA = (A0==0)==exp['k4_opt']                       # the criterion: A_F zero-free
    rec=dict(file=fn,mu=mu,z=z,A_zeros=A0,k3_rows=len(r3),k3_max=max3,k4_rows=len(r4),k4_max=max4,
             k4_hists=sorted({tuple(sorted(h.items())) for h in r4}),optimum_k4=opt4,
             level8_optimal=ok3,stays_optimal_k4=(max4==opt4),criterion_A_zero_free=(A0==0),pass_=ok3 and ok4 and okA)
    res.append(rec); bad+=not rec['pass_']; print(json.dumps(rec))
json.dump(res,open(os.path.join(here,'cross_level_regression.json'),'w'),indent=1)
if bad: print('CROSS_LEVEL_REGRESSION FAIL',bad); sys.exit(1)
print('CROSS_LEVEL_REGRESSION OK',len(res),'cases')
