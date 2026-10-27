# R03-02: positive and negative tests for the branch invariant E_F (Claude). Exit 0 iff every expectation holds.
import sys, random, json
sys.path.insert(0,'.')
from inv import Field, Ring, read_terms, invariants, res, div
m=5; K=Field(m); q=K.q; R8=Ring(m,8); random.seed(20261025)
def rnd(): return tuple(random.randrange(8) for _ in range(m))
def S(T,x,tau):
    x1=R8.add(x,tau); x2=R8.add(x1,tau)
    return R8.sub(R8.add(R8.ev(T,x2),R8.ev(T,x)),R8.add(R8.ev(T,x1),R8.ev(T,x1)))
def E(T,x,tau):
    s=S(T,x,tau); assert all(v%4==0 for v in s); return res(div(s,4,8))
def twice(t): return tuple((2*v)%8 for v in t)
out={}; bad=0
for fn in ['c0_A1.txt','F1_c0A1_plus2X2.txt','P53nat.txt','P53sp.txt','c1nat.txt']:
    T=read_terms(fn,m); iv=invariants(T,m); rho=iv['rho']; mu=iv['mu']; A=iv['A']; Z=iv['Z']
    rec=dict(rho=rho,mu=mu,z=len(Z))
    # P1: lift independence (x -> x+2u, tau -> tau+2v), 20 random trials per a in Z
    p1=True
    for a in Z:
        base=E(T,R8.lift(a),R8.lift(rho))
        for _ in range(20):
            x=R8.add(R8.lift(a),twice(rnd())); tau=R8.add(R8.lift(rho),twice(rnd()))
            p1 &= (E(T,x,tau)==base)
    rec['P1_lift_independent']=p1
    # P2: translation identity E(a+rho)+E(a) = rho*A(a)+rho^2*mu
    p2=all(iv['E'][a]^iv['E'][a^rho]==K.mul(rho,A[a])^K.mul(K.mul(rho,rho),mu) for a in Z)
    rec['P2_translation_identity']=p2
    # P3: chi is rho-periodic when defined
    p3=all(iv['chi'].get(a)==iv['chi'].get(a^rho) for a in Z)
    rec['P3_chi_periodic']=p3
    # N1: E itself is NOT rho-periodic in general (expected False somewhere unless rho*A+rho^2*mu==0 on Z)
    rec['N1_E_periodic_somewhere_fails']=any(iv['E'][a]!=iv['E'][a^rho] for a in Z) or all(K.mul(rho,A[a])^K.mul(K.mul(rho,rho),mu)==0 for a in Z)
    # N2: off Z the numerator is not divisible by 4 (E undefined): expect failure for every a not in Z
    offZ=[a for a in range(q) if a not in Z]
    rec['N2_offZ_not_div4']=all(any(v%4 for v in S(T,R8.lift(a),R8.lift(rho))) for a in offZ)
    # P5: exact telescoping of the SUM: S(x+tau)+S(x) == G(x+2tau)-G(x) in R_3, G(X)=F(X+tau)-F(X), all a
    def Gf(x,tau): return R8.sub(R8.ev(T,R8.add(x,tau)),R8.ev(T,x))
    p5=True; n3=False
    for a in range(q):
        x=R8.lift(a); tau=R8.lift(rho); x1=R8.add(x,tau); x2=R8.add(x1,tau)
        lhs=R8.add(S(T,x1,tau),S(T,x,tau)); rhs=R8.sub(Gf(x2,tau),Gf(x,tau))
        p5 &= (lhs==rhs)
        if R8.sub(S(T,x1,tau),S(T,x,tau))!=rhs: n3=True
    rec['P5_sum_telescopes_exactly']=p5
    # N3: the third difference S(x+tau)-S(x) does not telescope to G(x+2tau)-G(x) (it differs by 2S(x), which is 0 mod 8 only on Z)
    rec['N3_third_difference_does_not_telescope']=n3 if len(Z)<q else 'n/a (Z=F_q: 2S=0 mod 8 everywhere)'
    # P4: F+2J^2 shifts E by (D_rho j)^2 and leaves A: J = X^5 + c X^3 (random unit coefficient)
    c=R8.lift(random.randrange(1,q))
    J=[(5,(1,)+(0,)*(m-1)),(3,c)]
    # 2J^2 = 2X^10 + 4cX^8 + 2c^2X^6  (mod 8)
    T2=T+[(10,(2,)+(0,)*(m-1)),(8,tuple((4*v)%8 for v in c)),(6,twice(R8.mul(c,c)))]
    iv2=invariants(T2,m)
    jf=lambda a: K.mul(a,K.mul(a,K.mul(a,K.mul(a,a))))^K.mul(res(c),K.mul(a,K.mul(a,a)))
    p4= iv2['A']==A and all(iv2['E'][a]==iv['E'][a]^K.mul(jf(a)^jf(a^rho),jf(a)^jf(a^rho)) for a in Z)
    rec['P4_2J2_shift']=p4
    # N4: F+2H with H' residue not rho-periodic-difference-free changes A (control: H = X^3, h = X^2, D_rho h = rho^2 != 0)
    T3=T+[(3,(2,)+(0,)*(m-1))]; iv3=invariants(T3,m)
    rec['N4_2X3_changes_A_by_rho2']=all(iv3['A'][a]==A[a]^K.mul(rho,rho) for a in range(q))
    for k_,v in rec.items():
        if k_.startswith(('P','N')) and v is False: bad+=1
    out[fn]=rec; print(fn,json.dumps(rec))
json.dump(out,open('e_tests.json','w'),indent=1)
if bad: print('E_TESTS FAIL',bad); sys.exit(1)
print('E_TESTS OK')
