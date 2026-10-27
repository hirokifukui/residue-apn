import sys, json, random
sys.path.insert(0, '/home/claude/w/research/sparse_r06')
from lifts import *
out = open('/home/claude/w/research/sparse_r06/out/lifts_%s.jsonl' % sys.argv[1], 'w')
m = int(sys.argv[1]); F = GF(m, POLY[m]); nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 0
cs = [c for c in range(2, F.q) if lin_invertible(F, Bco(F, c))]
if nsamp: random.seed(m); cs = sorted(random.sample(cs, nsamp))
agg = dict(m=m, tested=0, Lp_formula_ok=0, flat_formula_ok=0, flat_zero_free=0, nat_zero_free=0, eps1=0)
for c in cs:
    r = build(m, c)
    out.write(json.dumps(r) + '\n')
    agg['tested'] += 1; agg['Lp_formula_ok'] += r['Lp_formula_ok']; agg['flat_formula_ok'] += r['A_flat_formula_ok']
    agg['flat_zero_free'] += (r['A_flat_zeros'] == 0); agg['nat_zero_free'] += (r['A_nat_zeros'] == 0); agg['eps1'] += r['eps']
out.write('SUMMARY ' + json.dumps(agg) + '\n'); print(json.dumps(agg))
