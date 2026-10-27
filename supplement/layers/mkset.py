# Generate the m=5 test set of lifts (term files) and an index.
import json, random, os
from grlib import *
from lifts import *
from pinv import pinv
m=5; F=Field(m); q=32; rng=random.Random(20261026)
os.makedirs('lifts',exist_ok=True)
reps=json.load(open('reps_m5.json'))
src={}
for key,v in reps.items():
    c={int(e):x for e,x in v['coeffs'].items()}
    tag='r'+''.join('1' if b=='True' else '0' for b in key.strip('()').replace(' ','').split(','))
    src[tag]=c
for nm in ['P53nat','c1nat','rep5_nat']:
    src[nm]=residue_coeffs(read_terms(f'../{nm}.txt',m),m)
index={}
for tag,c in src.items():
    P=pinv(c,m); rho=P['rho']
    nat=natural(c,m)
    variants={'nat':nat,'A1':set_A(nat,m,rho,[1]*q),'A0':set_A(nat,m,rho,[0]*q)}
    # A with one zero pair
    tgt=[1]*q; a0=rng.randrange(q); tgt[a0]=0; tgt[a0^rho]=0
    variants['Az']=set_A(nat,m,rho,tgt)
    variants['rnd']=rand_pert(variants['A1'],m,rng)
    variants['rnd2']=rand_pert(nat,m,rng)
    for vn,T in variants.items():
        fn=f'lifts/{tag}_{vn}.txt'; write_terms(fn,T)
        index[f'{tag}_{vn}']=dict(file=fn,rho=rho,mu=P['mu'],c3=P['c3'],pi_zeros=P['pi_zeros'],Z=len(P['Z']),A_zero=A_of(T,m,rho).count(0))
json.dump(index,open('lifts/index.json','w'),indent=0)
print(len(index))
for k,v in index.items(): print(k,v)
