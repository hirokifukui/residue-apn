# Residue-level invariants of p (depend only on p): rho, mu, c2, c3, pi = p^[2], zeros, Z.
import sys, json
from grlib import *
def binom2(e,i):
    from math import comb
    return comb(e,i)&1
def peval(F,c,a,der=0):
    r=0
    for e,v in c.items():
        if e>=der and binom2(e,der):
            r^=F.mul(v,F.pow(a,e-der)) if e-der>0 else v
    return r
def pinv(c,m):
    F=Field(m); q=F.q
    p=[peval(F,c,a) for a in range(q)]
    assert len(set(p))==q, "not perm"
    for d in range(1,q):
        cnt={}
        for a in range(q): cnt[p[a^d]^p[a]]=cnt.get(p[a^d]^p[a],0)+1
        assert max(cnt.values())==2,"not APN"
    for e in c: assert bin(e).count('1')<=2 and e<q, "not reduced quadratic"
    dp=[peval(F,c,a,1) for a in range(q)]
    assert 0 not in dp
    rhos=[r for r in range(1,q) if dp[r]==dp[0]]
    assert len(rhos)==1
    rho=rhos[0]
    # (H): K = p'-p'(0) linear with kernel {0,rho}; eps = p'(0) not in K(F_q)
    Kimg={dp[a]^dp[0] for a in range(q)}
    assert dp[0] not in Kimg
    pi=[peval(F,c,a,2) for a in range(q)]
    mu=pi[rho]^pi[0]
    c2=c.get(2,0); c3=c.get(3,0)
    Lam=[p[a^rho]^p[a]^F.mul(rho,dp[a]) for a in range(q)]
    Z=[a for a in range(q) if Lam[a]==0]
    pizeros=[a for a in range(q) if pi[a]==0]
    l1=[pi[a]^pi[0] for a in range(q)]
    rk=len(set(l1)).bit_length()-1
    # for j=1: w_u(a)=pi(a)+u*c3 ; units u with zero-free w_u
    bad_u=[u for u in range(1,q) if any(pi[a]^F.mul(u,c3)==0 for a in range(q))]
    return dict(rho=rho,mu=mu,c2=c2,c3=c3,Z=Z,pi_zeros=pizeros,l1_rank=rk,bad_u_j1=bad_u,pi=pi)
if __name__=="__main__":
    m=int(sys.argv[1]); T=read_terms(sys.argv[2],m)
    c=residue_coeffs(T,m); d=pinv(c,m); d.pop('pi'); print(json.dumps(d))
