#!/usr/bin/env python3
"""Check: P_{m,r} = sigma^{m-2} o X^3 o T_r (sigma = Frobenius, T_r = sum_{i<r} X^{2^i})
equals R_q(A^3) with A = T_r^{2^{m-2}} (linearized), i.e. lies in the scope of BS v3 Cor 6.2,
and that BS v3 Rem 6.3 (A = x + x^{q/4} + x^{q/2}) is P_{m,3}. Also evaluates the Cor 6.2 trace
condition and the residue cell (rho, mu, |Z|). Output JSON to argv[1]."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bs_trace_residue import GF2m, deriv, analyse

def reduced_cube(F, a):
    m, q = F.m, F.q
    res = {}
    for i, ai in enumerate(a):
        for j, aj in enumerate(a):
            e = (1 << i) + (1 << (j + 1)); e = 1 + (e - 1) % (q - 1)
            res[e] = res.get(e, 0) ^ F.mul(ai, F.mul(aj, aj))
    return {e: c for e, c in res.items() if c}

out = []
for m, mod in [(5, 0b100101), (7, 0b10000011)]:
    F = GF2m(m, mod); q = F.q
    for r in range(3, m + 1, 2):
        Tr_ = lambda x: [x := x] and 0
        def T(x, r=r):
            s, y = 0, x
            for _ in range(r):
                s ^= y; y = F.mul(y, y)
            return s
        inv = len({T(x) for x in range(q)}) == q
        if not inv:
            out.append({"m": m, "r": r, "T_r_invertible": False}); continue
        a = [0] * m
        for i in range(r):
            a[(i + m - 2) % m] ^= 1
        p = reduced_cube(F, a)
        func_ok = all(F.ev(p, x) == F.pow(F.pow(T(x), 3), 1 << (m - 2)) for x in range(q))
        cond = a[0] and a[m - 1] and F.tr(F.mul(F.mul(a[0], F.mul(a[m - 2], a[m - 2])), F.inv(F.pow(a[m - 1], 3)))) == 1
        res = analyse(F, p, f"P_{{{m},{r}}}")
        rem63 = sorted(p) == [1, 2, 3, 9, 10, 18, 24] if (m, r) == (5, 3) else None
        out.append({"m": m, "r": r, "T_r_invertible": True, "A_coeff_support": [j for j in range(m) if a[j]],
                    "R_q(A^3)_equals_P_mr_as_function": func_ok, "reduced_poly_exponents": sorted(p),
                    "Cor6.2_condition_holds": bool(cond), "p_prime_zero_free": res["p_prime_zero_free"],
                    "satisfies_H": res["satisfies_H"], "rho": res.get("rho"), "mu": res.get("mu"),
                    "absZ": res.get("absZ"), "equals_BS_Rem6.3_m5_example": rem63})
        print(out[-1])
json.dump(out, open(sys.argv[1], "w"), indent=1)
