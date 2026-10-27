#!/usr/bin/env python3
"""Construct a lift of the BS v3 trace polynomial (m=5, w=theta) with A_F == 0 and test Delta_exc.

Mechanism (k=3): for xbar=a, x = t+2u,
   D_alpha F(t+2u) == D_alpha F(t) + 4( ubar*A_F(a) + ubar^2 * mu )   (mod 8),
so with mu != 0 the multiplicity on one residue class is q if A_F(a)=0 and 2q if A_F(a)!=0.
Hence, in the cell (mu!=0, Z=empty), a lift reaching q at k=3 must have A_F == 0.
A_F is rho-periodic and A_{F+2H} = A_F + D_rho h (h = residue function of H'), so we solve
D_rho h = A_F0 over F_2 for h in the span of b*a^d (wt(d)<=2), and set
H = sum h_d X^(2e_d+1) with 2 e_d == d (mod q-1).
"""
import json, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bs_trace_residue import GF2m, trace_family  # noqa: E402
from bs_trace_lift_k3 import GR, digits, lift_poly, A_function, exceptional_rows  # noqa: E402

F5 = GF2m(5, 0b100101)
q = 32


def solve_gf2(cols, target):
    """cols: list of int bitvectors (length n), target int; return subset indices or None."""
    basis = {}  # pivot -> (vec, combo)
    for i, v in enumerate(cols):
        combo = 1 << i
        while v:
            piv = v.bit_length() - 1
            if piv in basis:
                bv, bc = basis[piv]
                v ^= bv; combo ^= bc
            else:
                basis[piv] = (v, combo)
                break
    v, combo = target, 0
    while v:
        piv = v.bit_length() - 1
        if piv not in basis:
            return None
        bv, bc = basis[piv]
        v ^= bv; combo ^= bc
    return [i for i in range(len(cols)) if combo >> i & 1]


def fvec(vals):
    return sum(v << (5 * a) for a, v in enumerate(vals))


def main():
    t0 = time.time()
    p = trace_family(F5, 2)
    rho = 31
    R3 = GR(3)
    A0 = A_function(R3, lift_poly(p), rho)
    assert all(A0[a] == A0[a ^ rho] for a in range(q))
    exps = sorted({d for d in range(0, q - 1) if bin(d).count("1") <= 2})
    cols, labels = [], []
    for d in exps:
        for b in [1, 2, 4, 8, 16]:
            vals = [F5.mul(b, F5.pow(a ^ rho, d) ^ F5.pow(a, d)) for a in range(q)]
            cols.append(fvec(vals)); labels.append((d, b))
    sol = solve_gf2(cols, fvec(A0))
    assert sol is not None
    hcoef = {}
    for i in sol:
        d, b = labels[i]
        hcoef[d] = hcoef.get(d, 0) ^ b
    hcoef = {d: c for d, c in hcoef.items() if c}
    inv2 = pow(2, -1, q - 1)
    H = {}
    for d, c in hcoef.items():
        e = (d * inv2) % (q - 1)
        H[2 * e + 1] = c
    extra = {E: 2 * digits(c) for E, c in H.items()}
    L = lift_poly(p, extra)
    A = A_function(R3, L, rho)
    print("h =", hcoef, " H =", H, " A_{F0+2H} =", A)
    best, hist, wa, na = exceptional_rows(R3, L, rho)
    print("Delta_exc(k=3) for F0+2H:", best, hist, f"[{time.time()-t0:.0f}s]")
    out = {"h_residue_function_coeffs(d->F32 int)": {str(d): c for d, c in hcoef.items()},
           "H_terms(E->F32 int, lift adds 2*[c]X^E)": {str(E): c for E, c in H.items()},
           "A_after": A, "A_identically_zero": all(v == 0 for v in A),
           "Delta_exc_k3": best, "row_max_histogram_k3": hist, "n_alpha_k3": na}
    # control: same H but with A shifted by a nonzero constant (add 2[b]X^3) -> A == const != 0
    L2 = lift_poly(p, {**extra, 3: (extra.get(3, 0 * digits(0)) + 2 * digits(1)) % 8})
    A2 = A_function(R3, L2, rho)
    best2, hist2, _, _ = exceptional_rows(R3, L2, rho)
    print("control (A == const", A2[0], "):", best2, hist2)
    out["control_A_const_nonzero"] = {"A": A2, "Delta_exc_k3": best2, "hist": hist2}
    # k=4: same digit lift read in GR(16,5); predicted minimax 2q=64 for every lift
    R4 = GR(4)
    L4 = lift_poly(p, extra, k=4)
    rng = np.random.default_rng(44)
    alphas = (digits(rho) + 2 * rng.integers(0, 8, size=(160, 5))) % 16
    best4, hist4, _, na4 = exceptional_rows(R4, L4, rho, alphas)
    print("k=4 sampled:", best4, hist4, f"[{time.time()-t0:.0f}s]")
    out["k4_sampled"] = {"n_alpha": na4, "sampled_max": best4, "hist": hist4}
    out["runtime_s"] = round(time.time() - t0, 1)
    json.dump(out, open(sys.argv[1] if len(sys.argv) > 1 else "bs_trace_lift_opt.json", "w"), indent=1)


if __name__ == "__main__":
    main()
