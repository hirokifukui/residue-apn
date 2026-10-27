from pathlib import Path
# R03-11: reconstruct a representative p = L(A(x)^d) from (A,L) column data, verify reduced-polynomial
# invariants (mu=0, Z empty), build the natural lift and an A==1 lift F_nat + 2H (H' residue = D_rho-correction),
# write terms files and a JSON certificate. Uses inv.py field/ring arithmetic; rsearch.c is the independent cross-check.
import sys, json, hashlib
sys.path.insert(0,'..')
from inv import Field, Ring, invariants
def lin(M,x):
    r=0
    for i,v in enumerate(M):
        if (x>>i)&1: r^=v
    return r
def build(m,d,A,L,tag):
    K=Field(m); q=K.q
    f=[lin(L,K.pow(lin(A,x),d)) for x in range(q)]
    assert len(set(f))==q, "not a permutation"
    # APN check (DDT max 2)
    for a in range(1,q):
        cnt={}
        for x in range(q):
            y=f[x^a]^f[x]; cnt[y]=cnt.get(y,0)+1
        assert max(cnt.values())==2
    c=[0]*q; c[0]=f[0]
    for e in range(1,q):
        s=0
        for x in range(1,q):
            if f[x]: s^=K.mul(f[x],K.pow(x,q-1-e))
        c[e]=s
    c[q-1]^=f[0]  # coefficient of X^{q-1} is sum over all x
    for x in range(q):
        acc=0
        for e in range(q):
            if c[e]: acc^=K.mul(c[e],K.pow(x,e))
        assert acc==f[x]
    deg=max(e for e in range(q) if c[e])
    nat=[(e,[(c[e]>>i)&1 for i in range(m)]) for e in range(q) if c[e]]
    iv=invariants(nat,m); rho=iv['rho']
    # correction to A==1: g = 1 + A (rho-periodic); h with h(a+rho)+h(a)=g(a); h=s^2; H=sum lift(s_e^2) X^{2e+1}
    g=[1^iv['A'][a] for a in range(q)]
    assert all(g[a]==g[a^rho] for a in range(q))
    h=[0]*q
    for a in range(q):
        if a<(a^rho): h[a^rho]=g[a]
    s=[K.pow(v,q//2) for v in h]
    S=[0]*q; S[0]=s[0]
    for e in range(1,q):
        t=0
        for x in range(1,q):
            if s[x]: t^=K.mul(s[x],K.pow(x,q-1-e))
        S[e]=t
    S[q-1]^=s[0]
    H=[(2*e+1,[2*((K.mul(S[e],S[e])>>i)&1) for i in range(m)]) for e in range(q) if S[e]]
    F1=nat+H
    iv1=invariants(F1,m)
    assert iv1['mu']==iv['mu']==0 and iv1['Z']==iv['Z'] and set(iv1['A'])=={1}
    out={}
    for name,T in (('nat',nat),('A1',F1)):
        fn=f"{tag}_{name}.txt"
        with open(fn,'w') as fh:
            fh.write(f"{len(T)}\n")
            for e,cd in T: fh.write(f"{e} "+" ".join(map(str,cd))+"\n")
        out[name]=dict(file=fn,sha256=hashlib.sha256(open(fn,'rb').read()).hexdigest(),terms=len(T),deg=max(e for e,_ in T))
    return dict(tag=tag,m=m,q=q,d=d,A_columns=A,L_columns=L,field_poly=Field(m).P,
                reduced_coeffs={str(e):c[e] for e in range(q) if c[e]},reduced_degree=deg,
                permutation=True,apn_ddt_max=2,rho=rho,mu=iv['mu'],Z=iv['Z'],z=len(iv['Z']),
                A_nat_zeros=iv['A'].count(0),A_after_correction=sorted(set(iv1['A'])),files=out,
                predicted_exceptional_spectrum_k3={str(q):q*q}, predicted_max=q)
if __name__=="__main__":
    recs=[]
    j=json.load(open(Path(__file__).with_name('rep5_seed.json')))
    recs.append(build(5,3,j['A'],j['L'],'rep5'))
    # first m=7 mu=0,z=0 hit from the C search log
    for line in open('m7_search.log'):
        if line.startswith('HIT') and ' z=0 ' in line:
            fl=dict(kv.split('=',1) for kv in line.split()[1:])
            A=list(map(int,fl['A'].split(','))); L=list(map(int,fl['L'].split(',')))
            recs.append(build(7,3,A,L,'rep7')); recs[-1]['search_hit_line']=line.strip(); break
    if [r['tag'] for r in recs]!=['rep5','rep7']:
        print('FAIL: expected records rep5 and rep7, got',[r['tag'] for r in recs],file=sys.stderr); sys.exit(3)
    json.dump(recs,open('representative_certificate.json','w'),indent=1)
    for r in recs: print(r['tag'],'rho',r['rho'],'mu',r['mu'],'z',r['z'],'Anat0',r['A_nat_zeros'],r['files'])
