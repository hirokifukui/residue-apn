# Zero-cost variant: F_u = F_nat with the X^5 coefficient replaced by f_5 + 2[u]; A_{F_u} = A_nat + u rho^4.
# Counts the u (in F_q) for which A_{F_u} is zero-free; verifies by brute force (gr aset) for a few u.
import sys, json, random
sys.path.insert(0, '/home/claude/w/research/sparse_r06')
from lifts import *
m = int(sys.argv[1]); F = GF(m, POLY[m]); out = []
cs = [c for c in range(2, F.q) if lin_invertible(F, Bco(F, c))]
if len(sys.argv) > 2: random.seed(m); cs = sorted(random.sample(cs, int(sys.argv[2])))
agg = dict(m=m, tested=0, min_good_fraction=1.0, nat_zero_free=0, u1_zero_free=0, brute_checks=0, brute_ok=0)
for c in cs:
    B = Bco(F, c); rho = solve_lin(F, B, 1)
    fn = '%s/terms/m%d_c%d_nat.txt' % (D, m, c); write_terms(nat_terms(F, c), fn)
    A = aset(m, 3, fn, rho)['A']; img = set(A); r4 = F.pow(rho, 4)
    good = [u for u in range(F.q) if F.mul(u, r4) not in img]
    agg['tested'] += 1; agg['min_good_fraction'] = min(agg['min_good_fraction'], len(good) / F.q)
    agg['nat_zero_free'] += (0 in good); agg['u1_zero_free'] += (1 in good)
    for u in random.sample(good, min(2, len(good))):
        T = nat_terms(F, c); add2(T, 5, F, u); fn2 = '%s/terms/m%d_c%d_u%d.txt' % (D, m, c, u); write_terms(T, fn2)
        z = aset(m, 3, fn2, rho)['zeros']; agg['brute_checks'] += 1; agg['brute_ok'] += (z == 0)
    out.append(dict(c=c, rho=rho, image_size=len(img), n_good_u=len(good)))
json.dump(dict(summary=agg, per_c=out), open('%s/out/zerocost_m%d.json' % (D, m), 'w'))
print(json.dumps(agg))
