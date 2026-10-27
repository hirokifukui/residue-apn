#!/usr/bin/env python3
"""Exceptional differential rows of lifts of the BS v3 Thm 2.4 trace polynomial
F_w (m=5, w=theta, modulus t^5+t^2+1) to GR(2^k,5) = (Z/2^k)[t]/(t^5+t^2+1).

* lift F0 = natural 0/1-digit lift of the residue polynomial p = F_w (coefficientwise)
* A_F(a) = residue of (F'(x+tau)-F'(x))/2, xbar=a, taubar=rho   (checked independent of reps)
* candidate lifts F0 + 2 b X^e   (e odd) which shift A by b*D_rho(a^(e-1))
* Delta_exc(F) = max over all alpha with alphabar = rho and all beta of
  delta_F(alpha,beta) = #{x in R_k : F(x+alpha) - F(x) = beta}
  computed exhaustively at k=3 (1024 exceptional alpha, |R_3| = 32768);
  at k=4 a random sample of exceptional alpha only (lower bound for Delta_exc).
numpy is used only to vectorise ring arithmetic over all of R_k.
"""
import json, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bs_trace_residue import GF2m, trace_family, deriv  # noqa: E402

M = 5
F5 = GF2m(5, 0b100101)
RED = np.array([1, 0, 1, 0, 0])  # t^5 = -(1 + t^2)


class GR:
    def __init__(self, k):
        self.k, self.mod = k, 1 << k
        self.N = self.mod ** M
        idx = np.arange(self.N)
        self.all = np.stack([(idx // self.mod ** i) % self.mod for i in range(M)], axis=1).astype(np.int64)
        self.w = self.mod ** np.arange(M)

    def index(self, X):
        return (X % self.mod) @ self.w

    def mul(self, A, B):
        # A,B shape (n,5) or (5,) broadcastable
        A = np.atleast_2d(A); B = np.atleast_2d(B)
        n = max(A.shape[0], B.shape[0])
        C = np.zeros((n, 2 * M - 1), dtype=np.int64)
        for i in range(M):
            for j in range(M):
                C[:, i + j] += A[:, i] * B[:, j]
        for d in range(2 * M - 2, M - 1, -1):  # reduce t^d = t^(d-5) * t^5 = -t^(d-5)(1+t^2)
            c = C[:, d].copy()
            C[:, d] = 0
            C[:, d - 5] -= c
            C[:, d - 3] -= c
        return C[:, :M] % self.mod

    def horner(self, coeffs, X):
        """coeffs: dict exponent -> (5,) int vector over Z/2^k; X: (n,5)."""
        deg = max(coeffs)
        R = np.tile(coeffs.get(deg, np.zeros(M, dtype=np.int64)), (X.shape[0], 1))
        for e in range(deg - 1, -1, -1):
            R = self.mul(R, X)
            if e in coeffs:
                R = (R + coeffs[e]) % self.mod
        return R


def digits(a):
    return np.array([(a >> i) & 1 for i in range(M)], dtype=np.int64)


def bits_to_int(v):
    return int(sum((int(v[i]) & 1) << i for i in range(M)))


def lift_poly(p, extra=None, k=3):
    """digit lift of residue poly p (dict e->F_32 int) plus extra dict e->vector (added)."""
    mod = 1 << k
    L = {e: digits(c) for e, c in p.items()}
    for e, v in (extra or {}).items():
        L[e] = (L.get(e, np.zeros(M, dtype=np.int64)) + v) % mod
    return {e: v for e, v in L.items() if v.any()}


def formal_derivative(L, mod):
    return {e - 1: (e * v) % mod for e, v in L.items() if e >= 1 and ((e * v) % mod).any()}


def A_function(R, L, rho, reps=None, rng=None):
    mod = R.mod
    dL = formal_derivative(L, mod)
    xs = np.stack([digits(a) for a in range(32)])
    tau = digits(rho)
    if reps is not None:  # perturb representatives by 2*random
        xs = (xs + 2 * rng.integers(0, mod, size=xs.shape)) % mod
        tau = (tau + 2 * rng.integers(0, mod, size=M)) % mod
    D = (R.horner(dL, (xs + tau) % mod) - R.horner(dL, xs)) % mod
    assert (D % 2 == 0).all(), "F'(x+tau)-F'(x) not divisible by 2"
    return [bits_to_int((D[a] // 2) % 2) for a in range(32)]


def exceptional_rows(R, L, rho, alphas=None):
    Fv = R.horner(L, R.all)                       # F on all of R_k
    Fidx = R.index(Fv)
    if alphas is None:  # all alpha with residue rho: alpha = digits(rho) + 2u, u in R_k / (2^(k-1))
        sub = R.mod // 2
        us = np.stack([(np.arange(sub ** M) // sub ** i) % sub for i in range(M)], axis=1)
        alphas = (digits(rho) + 2 * us) % R.mod
    best, hist = 0, {}
    worst_alpha = None
    for al in alphas:
        xi = R.index(R.all + al)
        D = (Fv[xi] - Fv) % R.mod
        cnt = np.bincount(R.index(D), minlength=R.N)
        mx = int(cnt.max())
        hist[mx] = hist.get(mx, 0) + 1
        if mx > best:
            best, worst_alpha = mx, al.tolist()
    return best, hist, worst_alpha, len(alphas)


def main():
    out = {}
    t0 = time.time()
    w = 2
    p = trace_family(F5, w)
    rho = 31
    out["residue_poly"] = {str(e): c for e, c in sorted(p.items())}
    out["rho"] = rho
    R3 = GR(3)
    L0 = lift_poly(p)
    A0 = A_function(R3, L0, rho)
    rng = np.random.default_rng(20261025)
    indep = all(A_function(R3, L0, rho, reps=True, rng=rng) == A0 for _ in range(8))
    out["A_F0"] = A0
    out["A_F0_independent_of_representatives_(8 random trials)"] = indep
    out["A_F0_zeros"] = [a for a in range(32) if A0[a] == 0]
    out["A_F0_image_size"] = len(set(A0))
    # affine check of A_F0
    aff = all(A0[a ^ b] ^ A0[a] ^ A0[b] ^ A0[0] == 0 for a in range(32) for b in range(32))
    out["A_F0_is_affine"] = aff
    print("A_F0:", A0, "zeros:", out["A_F0_zeros"], "affine:", aff, "indep:", indep)

    # shift check for 2 b X^3 : A should move by b*rho^2
    shift_ok = True
    for b in [1, 2, 7, 19]:
        Lb = lift_poly(p, {3: 2 * digits(b)})
        Ab = A_function(R3, Lb, rho)
        c = F5.mul(b, F5.mul(rho, rho))
        shift_ok &= all(Ab[a] == A0[a] ^ c for a in range(32))
    out["shift_formula_2bX3_verified"] = shift_ok
    print("shift formula ok:", shift_ok)

    results = []
    cands = [("F0", {})]
    for b in range(1, 32):
        cands.append((f"F0+2[{b}]X^3", {3: 2 * digits(b)}))
    cands += [("F0+2X^2", {2: 2 * digits(1)}), ("F0+2X^5", {5: 2 * digits(1)}),
              ("F0+2X^7", {7: 2 * digits(1)}), ("F0+4X^3", {3: 4 * digits(1)})]
    for name, extra in cands:
        L = lift_poly(p, extra)
        A = A_function(R3, L, rho)
        zf = 0 not in A
        best, hist, wa, na = exceptional_rows(R3, L, rho)
        results.append({"lift": name, "A_zero_free": zf, "A_num_zeros": A.count(0),
                        "Delta_exc_k3": best, "row_max_histogram": hist, "n_alpha": na,
                        "argmax_alpha": wa})
        print(name, "A zero-free:", zf, "#zeros", A.count(0), "Delta_exc(k=3) =", best, hist,
              f"[{time.time()-t0:.0f}s]")
    out["k3_results"] = results
    out["k3_min_Delta_exc_over_tested"] = min(r["Delta_exc_k3"] for r in results)
    out["k3_max_Delta_exc_over_tested"] = max(r["Delta_exc_k3"] for r in results)

    # k=4 sampled rows for one optimal k=3 lift (zero-free A) and for F0
    R4 = GR(4)
    rng = np.random.default_rng(4)
    k4 = []
    zf_names = [r["lift"] for r in results if r["A_zero_free"]][:1] + ["F0"]
    for name in zf_names:
        extra = dict(cands)[name]
        extra4 = {e: v.copy() for e, v in extra.items()}  # same Z-digit vector, read in Z/16
        L = lift_poly(p, extra4, k=4)
        us = rng.integers(0, 8, size=(96, M))
        alphas = (digits(rho) + 2 * us) % 16
        best, hist, wa, na = exceptional_rows(R4, L, rho, alphas)
        k4.append({"lift": name + " (same digits, read in GR(16,5))", "sampled_alpha": na,
                   "sampled_max": best, "row_max_histogram": hist})
        print("k=4", name, best, hist, f"[{time.time()-t0:.0f}s]")
    out["k4_sampled"] = k4
    out["runtime_s"] = round(time.time() - t0, 1)
    json.dump(out, open(sys.argv[1] if len(sys.argv) > 1 else "bs_trace_lift_k3.json", "w"), indent=1)


if __name__ == "__main__":
    main()
