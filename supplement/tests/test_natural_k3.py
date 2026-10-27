# R05-07 (Claude): Corollary natural (paper Section 6). For r >= 5 the natural lift of P_{m,r} over GR(8,m) has,
# in every exceptional row, n_{2q} = q(q-2)/2 and either n_{q^2} = 2 (r = 1 mod 4) or n_{2q^2} = 1 (r = 3 mod 4).
# Checked against (a) all 16384 exceptional rows of P_{7,5} (validate_v3_P75.json, full replay F3) and
# (b) two sampled exceptional rows each of P_{9,5} and P_{9,7} (natural/P9{5,7}nat_k3.out, grddt3 9 3 529 <terms> 2 1;
# field polynomial t^9+t^4+1, seed 1). Also checks that natural/P9rnat.txt is the natural lift (3r-2 monomials).
import os, sys, json
here=os.path.dirname(os.path.abspath(__file__)); root=os.path.dirname(here); os.chdir(root)
def pred(m,r):
    q=2**m; h={2*q: q*(q-2)//2}
    if r%4==1: h[q*q]=2
    else: h[2*q*q]=1
    return dict(sorted(h.items()))
def terms(m,r):
    w,u,v=2**(r-2),2**(m-2),2**(m-1)
    E=[1,2,w,w+1,w+2,w+u,w+v,u+1,u+2,u+v]
    for i in range(r-4):
        t=2**(i+2); E+=[t,w+t,u+t]
    return sorted(E)
res=[]
need_p75=os.environ.get('NATURAL_REQUIRE_P75')=='1'
if need_p75 and not os.path.exists('validate_v3_P75.json'):
    sys.exit('NATURAL_K3 FAIL: validate_v3_P75.json required but missing')
# (a) P75 full (required in the full replay, NATURAL_REQUIRE_P75=1; the core replay deletes the file in stage 0)
if need_p75:
    rec=[x for x in json.load(open('validate_v3_P75.json')) if x['file']=='P75nat.txt'][0]
    assert rec['n_exc_rows']==16384
    hs=[dict((int(a),int(b)) for a,b in h) for h in rec['exc_hists']]
    ok=len(hs)==1 and hs[0]==pred(7,5)
    res.append(dict(case='P75nat_all_rows', rows=rec['n_exc_rows'], hist=hs, pred=pred(7,5), ok=ok)); assert ok
# (b) P95, P97 samples
for m,r in [(9,5),(9,7)]:
    L=open(f'natural/P{m}{r}nat.txt').read().split('\n')
    n=int(L[0]); E=sorted(int(l.split()[0]) for l in L[1:1+n])
    assert n==3*r-2 and E==terms(m,r)
    rows=[l for l in open(f'natural/P{m}{r}nat_k3.out') if l.startswith('exc ')]
    assert len(rows)>=2
    for l in rows:
        h=dict((int(a),int(b)) for a,b in (t.split('x') for t in l.split('|')[1].split()))
        ok=h==pred(m,r); res.append(dict(case=f'P{m}{r}nat_sample', row=l.split()[1], hist=h, pred=pred(m,r), ok=ok)); assert ok
json.dump(res, open('tests/natural_k3_full.json' if need_p75 else 'tests/natural_k3.json','w'), indent=1)
assert len(res)==(5 if need_p75 else 4), len(res)
print('NATURAL_K3 OK', len(res), '(with P75 full rows)' if need_p75 else '(P95/P97 samples)')
