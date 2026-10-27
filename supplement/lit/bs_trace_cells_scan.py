#!/usr/bin/env python3
"""Scan all admissible w (T(w)=T(1/w)=0) of the BS v3 Thm 2.4 trace family for m=5,7,9
and tabulate the (mu, Z) cell of each member. Output JSON to argv[1]."""
import json, os, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bs_trace_residue import GF2m, trace_family, deriv

def cell(F, p):
    q = F.q
    dp = deriv(p); eps = dp.get(0, 0); Kp = {e: c for e, c in dp.items() if e}
    ker = [x for x in range(q) if F.ev(Kp, x) == 0]
    assert len(ker) == 2
    rho = ker[1]
    mu = 0
    for e, c in p.items():
        if e != 2 and e & 2:
            mu ^= F.mul(c, F.pow(rho, e - 2))
    Z = [a for a in range(q) if F.ev(p, a ^ rho) ^ F.ev(p, a) ^ F.mul(rho, F.ev(dp, a)) == 0]
    return rho, mu, len(Z)

out = {}
for m, mod in [(5, 0b100101), (7, 0b10000011), (9, (1 << 9) | (1 << 4) | 1)]:
    F = GF2m(m, mod)
    adm = [w for w in range(1, F.q) if F.tr(w) == 0 and F.tr(F.inv(w)) == 0]
    rows = []
    for w in adm:
        rho, mu, z = cell(F, trace_family(F, w))
        rows.append({"w": w, "rho": rho, "mu": mu, "absZ": z})
    cnt = Counter(("mu=0" if r["mu"] == 0 else "mu!=0", "Z=empty" if r["absZ"] == 0 else "Z!=empty") for r in rows)
    out[f"m={m}"] = {"modulus": bin(mod), "n_admissible_w": len(adm),
                     "cell_counts": {",".join(k): v for k, v in cnt.items()}, "members": rows}
    print(m, len(adm), dict(cnt), Counter(r["absZ"] for r in rows))
json.dump(out, open(sys.argv[1], "w"), indent=1)
