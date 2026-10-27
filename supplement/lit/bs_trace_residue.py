#!/usr/bin/env python3
"""Residue-level checks for members of the Bartoli-Stanica v3 Theorem 2.4 trace family
F_w(x) = x^3 + w x^2 T(x) + w^2 x T(x) + w^3 T(x)   (T = absolute trace polynomial),
plus two other BS v3 examples (Thm 5.1 degree-24, Rem 6.3 seven-term) and P_m of Thm 2.3.

For each polynomial p we check: reduced, quadratic (binary weight <= 2), permutation, APN,
write p' = eps + K(X) with K linearized, compute ker K, rho, eps in K(F_q)?, then
mu = [X^2](p(X+rho)+p(X)), Lambda(a) = p(a+rho)+p(a)+rho p'(a), Z = Lambda^{-1}(0).
Pure Python; F_{2^m} elements are ints (bit i = coefficient of t^i).
"""
import json, sys
from collections import Counter


class GF2m:
    def __init__(self, m, modulus):
        self.m, self.mod, self.q = m, modulus, 1 << m

    def mul(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a & self.q:
                a ^= self.mod
        return r

    def pow(self, a, e):
        r = 1
        while e:
            if e & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            e >>= 1
        return r

    def inv(self, a):
        return self.pow(a, self.q - 2)

    def tr(self, a):
        r = 0
        for _ in range(self.m):
            r ^= a
            a = self.mul(a, a)
        return r

    def ev(self, poly, x):
        r = 0
        for e, c in poly.items():
            r ^= self.mul(c, self.pow(x, e))
        return r


def add_term(p, e, c):
    p[e] = p.get(e, 0) ^ c
    if p[e] == 0:
        del p[e]


def deriv(p):
    return {e - 1: c for e, c in p.items() if e & 1}


def trace_family(F, w):
    m = F.m
    w2, w3 = F.mul(w, w), F.pow(w, 3)
    p = {}
    add_term(p, 3, 1)
    for i in range(m):
        add_term(p, 2 + (1 << i), w)
        add_term(p, 1 + (1 << i), w2)
        add_term(p, 1 << i, w3)
    return p


def analyse(F, p, name):
    q, m = F.q, F.m
    out = {"name": name, "m": m, "modulus": bin(F.mod), "poly": {str(e): c for e, c in sorted(p.items())}}
    out["degree"] = max(p)
    out["reduced"] = max(p) < q
    out["quadratic"] = all(bin(e).count("1") <= 2 for e in p)
    vals = [F.ev(p, x) for x in range(q)]
    out["permutation"] = len(set(vals)) == q
    du = 0
    spec = Counter()
    for a in range(1, q):
        row = Counter(vals[x ^ a] ^ vals[x] for x in range(q))
        du = max(du, max(row.values()))
        spec.update(row.values())
    out["diff_uniformity"] = du
    out["APN"] = du == 2
    dp = deriv(p)
    eps = dp.get(0, 0)
    Kp = {e: c for e, c in dp.items() if e != 0}
    out["eps"] = eps
    out["K_terms"] = {str(e): c for e, c in sorted(Kp.items())}
    out["K_linearized"] = all(e & (e - 1) == 0 for e in Kp)
    Kv = [F.ev(Kp, x) for x in range(q)]
    ker = [x for x in range(q) if Kv[x] == 0]
    out["ker_K"] = ker
    out["eps_in_image_K"] = eps in set(Kv)
    dvals = [eps ^ v for v in Kv]
    out["p_prime_zero_free"] = 0 not in dvals
    out["p_prime_fiber_sizes"] = sorted(set(Counter(dvals).values()))
    H = (out["reduced"] and out["quadratic"] and out["permutation"] and out["APN"]
         and out["K_linearized"] and len(ker) == 2 and not out["eps_in_image_K"])
    out["satisfies_H"] = H
    if len(ker) == 2:
        rho = ker[1]
        out["rho"] = rho
        # mu = [X^2](p(X+rho)+p(X)) : sum over e != 2 with bit 1 set (Lucas) of c_e rho^(e-2)
        mu = 0
        for e, c in p.items():
            if e != 2 and (e & 2):
                mu ^= F.mul(c, F.pow(rho, e - 2))
        out["mu"] = mu
        Lam = [F.ev(p, a ^ rho) ^ vals[a] ^ F.mul(rho, F.ev(dp, a)) for a in range(q)]
        Z = [a for a in range(q) if Lam[a] == 0]
        out["Lambda_values"] = Lam
        out["Z"] = Z
        out["absZ"] = len(Z)
        cell = ("mu=0" if mu == 0 else "mu!=0") + "," + ("Z=empty" if not Z else "Z!=empty")
        out["cell"] = cell
        pred = {"mu=0,Z=empty": "q at all k",
                "mu=0,Z!=empty": "2q at all k",
                "mu!=0,Z=empty": "q at k=3, 2q at k>=4",
                "mu!=0,Z!=empty": "2q at all k"}[cell]
        out["predicted_minimax_Delta_exc"] = pred
    return out


def main():
    results = []
    F5 = GF2m(5, 0b100101)          # t^5+t^2+1
    F7 = GF2m(7, 0b10000011)        # t^7+t+1
    # BS v3 Cor 6.4 / Rem 6.5 member: w = theta (root of t^5+t^2+1) -> int 2
    adm5 = [w for w in range(1, 32) if F5.tr(w) == 0 and F5.tr(F5.inv(w)) == 0]
    print("m=5 admissible w:", adm5)
    results.append(analyse(F5, trace_family(F5, 2), "BS v3 Thm 2.4 trace family, m=5, w=theta (int 2)"))
    adm7 = [w for w in range(1, 128) if F7.tr(w) == 0 and F7.tr(F7.inv(w)) == 0]
    print("m=7 admissible w (count):", len(adm7), "first:", adm7[:5])
    results.append(analyse(F7, trace_family(F7, adm7[0]), f"BS v3 Thm 2.4 trace family, m=7, w=int {adm7[0]}"))
    # all ten admissible w for m=5: summary only
    summary5 = []
    for w in adm5:
        r = analyse(F5, trace_family(F5, w), f"m=5 w={w}")
        summary5.append({k: r.get(k) for k in ["name", "satisfies_H", "rho", "mu", "absZ", "cell"]})
    # Other BS v3 examples
    zh = dict(zip([0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24],
                  [30, 30, 31, 12, 3, 30, 29, 9, 27, 7, 5, 9, 26, 11, 28, 6]))
    results.append(analyse(F5, zh, "BS v3 Thm 5.1 (Zhang-Haobo degree-24), m=5"))
    r63 = {e: 1 for e in [1, 2, 3, 9, 10, 18, 24]}
    results.append(analyse(F5, r63, "BS v3 Rem 6.3 seven-term R_32((x+x^8+x^16)^3), m=5"))
    P5 = {e: 1 for e in [1, 4, 6, 10, 12, 20, 24]}
    results.append(analyse(F5, P5, "BS v3 Thm 2.3 P_5 (constant derivative)"))
    P7 = {e: 1 for e in [1, 4, 10, 18, 24, 72, 80]}
    results.append(analyse(F7, P7, "BS v3 Thm 2.3 P_7 (constant derivative)"))
    for r in results:
        print({k: r.get(k) for k in ["name", "degree", "reduced", "quadratic", "permutation", "APN",
                                     "eps", "K_terms", "ker_K", "eps_in_image_K", "p_prime_fiber_sizes",
                                     "satisfies_H", "rho", "mu", "Z", "cell", "predicted_minimax_Delta_exc"]})
    print("m=5 all admissible w:")
    for s in summary5:
        print(s)
    json.dump({"examples": results, "m5_all_admissible_w": summary5},
              open(sys.argv[1] if len(sys.argv) > 1 else "bs_trace_residue.json", "w"), indent=1)


if __name__ == "__main__":
    main()
