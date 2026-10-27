# Representatives with μ = 0 and Z = ∅ for every odd m ≥ 5

Status: **open problem (1) of Section "Representatives, applications and open problems" is settled affirmatively**
by an explicit one-parameter family with a complete proof. The only non-elementary input is the Weil bound for
binary Kloosterman sums, which is needed to show that the parameter exists. The parameter is not given by a closed
formula. Its existence is proved, and admissible values are listed for m ≤ 13 and sampled up to m = 31.

## 1. Statement

Let m ≥ 5 be odd, q = 2^m, Tr the absolute trace, T_0 = {t ∈ F_q : Tr t = 0}. For d ∈ F_q put

  A_d(x) = Tr(x) + d·x^{2^{m-2}}  (coefficients a_i = 1 for i ≠ m−2, a_{m−2} = 1 + d),

and let p_d ∈ F_q[X] be the reduced polynomial (deg < q) of the function x ↦ A_d(x)^3.

**Theorem.** Suppose d ≠ 0 and Tr(1/d) = 0. Then:
1. A_d is invertible, and p_d is a reduced quadratic APN permutation.
2. p_d' = ε + K with ε = (1+d)^2 and K(y) = A_d(y)^2 + A_d(y). We have ker K = {0, ρ} with ρ = d^{−4}, and
   Im K = T_0.
3. μ = 0.
4. Λ(a) = (1 + ρ)(w^2 + w) + 1 + ρ(1+d)^2 with w = A_d(a), and Λ has no zero: **Z = ∅**.
5. p_d satisfies (H) **iff Tr(d) = 0**.

So for every d with Tr(d) = Tr(1/d) = 0, p_d satisfies (H) with μ = 0 and Z = ∅. Inside the family {p_d}, these
conditions hold exactly for such d: for Tr(1/d) = 1 the map A_d is singular, and for Tr(d) = 1 we have ε ∈ Im K.

**Existence.** N(m) := #{d ∈ F_q^* : Tr d = Tr d^{−1} = 0} = (q − 3 + K_m)/4, where
K_m = Σ_{x∈F_q^*} (−1)^{Tr(x + 1/x)}. Weil's bound |K_m| ≤ 2√q gives N(m) ≥ (q − 3 − 2√q)/4 > 0 for q ≥ 16, so N(m) ≥ 5
for every odd m ≥ 5. **Hence for every odd m ≥ 5 there are representatives satisfying (H) with μ = 0 and Z = ∅.**
There are N(m) of them (distinct polynomials) in this family alone. (Remark: this is the same admissibility
condition Tr(w) = Tr(w^{−1}) = 0 as in the Bartoli–Stănică family.)

## 2. Proof

### 2.1 General formulas for p = A(x)^3 (L = id), A = Σ a_i x^{2^i} invertible, m ≥ 5 odd
Indices are taken mod m.

*Reduced polynomial.* As functions, A(x)^3 = A(x)^2 A(x) = Σ_{i,j} a_i^2 a_j x^{2^{i+1}+2^j}, using x^{2^m} = x. A pair
with i+1 ≡ j gives the linear monomial x^{2^{j+1}}. Every other pair gives the DO monomial x^{2^u+2^v} with u ≠ v.
All exponents are < q and pairwise distinct as integers, so after collecting terms this is the reduced polynomial:
- c_{uv} = a_{u−1}^2 a_v + a_{v−1}^2 a_u (coefficient of X^{2^u+2^v}, u ≠ v, symmetric);
- l_w = a_{w−2}^2 a_{w−1} (coefficient of X^{2^w}).

In particular p is reduced and quadratic. Since gcd(3, 2^m − 1) = 1 for odd m, x^3 is an APN permutation, and composing
with an invertible linear A preserves both properties.

*Formal derivative.* (X^{2^u+2^v})' is X^{2^v} if u = 0 and 0 otherwise. (X^{2^w})' is 1 if w = 0 and 0 otherwise.
Hence ε = l_0 = a_{m−2}^2 a_{m−1} and
 K(y) = Σ_{v≥1} (a_{m−1}^2 a_v + a_{v−1}^2 a_0) y^{2^v} = a_{m−1}^2 A(y) + a_0 A(y)^2.
(The two y^1 terms a_{m−1}^2 a_0 y cancel.)

*Kernel and image of K.* Assume a_0 a_{m−1} ≠ 0 and put r = a_{m−1}^2/a_0. Then K(y) = a_0 w(w + r) with w = A(y).
So ker K = A^{−1}{0, r} = {0, ρ} with ρ = A^{−1}(r), and Im K = a_0 r^2·{v^2 + v} = a_0 r^2 T_0. Therefore
ε ∉ Im K ⇔ Tr(ε/(a_0 r^2)) = 1.

*μ.* In p(X+ρ) + p(X) the DO term c_{uv}X^{2^u+2^v} contributes c_{uv}(ρ^{2^v}X^{2^u} + ρ^{2^u}X^{2^v}) plus a constant, and
linear terms contribute only constants. Hence μ = [X^2] = Σ_{v≠1} c_{1v} ρ^{2^v}. Substituting c_{1v}:
 μ = a_0^2(A(ρ) − a_1ρ^2) + a_1(A(ρ)^2 − a_0^2ρ^2) = a_0^2 r + a_1 r^2.

*Λ.* Write w = A(a). Then p(a+ρ) + p(a) = (w+r)^3 + w^3 = r w^2 + r^2 w + r^3, and p'(a) = ε + a_0(w^2 + r w). So
 Λ(a) = (r + a_0ρ)(w^2 + r w) + r^3 + ρε.
If r ≠ a_0ρ, then a ↦ w is bijective and Im(Λ − Λ(const)) = (r + a_0ρ) r^2 T_0. So
 Z = ∅ ⇔ Tr((r^3 + ρε) / ((r + a_0ρ) r^2)) = 1.

### 2.2 Specialisation to A_d
Because m ≥ 5, the index m−2 differs from 0, 1 and m−1, so a_0 = a_1 = a_{m−1} = 1 and a_{m−2} = 1 + d. Hence r = 1.
- *Invertibility.* If A_d(x) = 0, then d x^{2^{m−2}} = Tr(x) ∈ {0, 1}. If Tr x = 0, then x = 0. If Tr x = 1, then
  x^{2^{m−2}} = 1/d, so x = d^{−4}, which needs Tr(d^{−4}) = Tr(1/d) = 1. Conversely, if Tr(1/d) = 1 then
  A_d(d^{−4}) = 1 + d·d^{−2^m} = 0. So A_d is invertible ⇔ d ≠ 0 and Tr(1/d) = 0.
- *ρ.* A_d(d^{−4}) = Tr(1/d) + d·d^{−1} = 1 = r, so ρ = d^{−4}.
- *μ* = a_0^2 r + a_1 r^2 = 1 + 1 = 0.
- *ε* = (1+d)^2·1. ε ∉ Im K = T_0 ⇔ Tr(1+d) = 1 ⇔ Tr(d) = 0 (since Tr 1 = 1 for odd m).
- *Z.* We have r + a_0ρ = 1 + d^{−4} ≠ 0 because d ≠ 1 (d = 1 has Tr(1/d) = 1). Then
  (1 + ρ(1+d)^2)/(1 + ρ) = (d^4 + d^2 + 1)/(d^4 + 1) = 1 + d^2/(d^2+1)^2,
  and Tr(d^2/(d^2+1)^2) = Tr(d/(d+1)^2) = Tr(1/(d+1)) + Tr(1/(d+1)^2) = 0. So the trace is 1 and Z = ∅, for every
  admissible d, with no condition on Tr(d).

### 2.3 Counting
N(m) = ¼ Σ_{d≠0} (1 + (−1)^{Tr d})(1 + (−1)^{Tr d^{−1}}) = ¼(q − 1 − 1 − 1 + K_m), because Σ_{d≠0}(−1)^{Tr d} = −1.
The Weil bound for Kloosterman sums, |K_m| ≤ 2√q, gives the stated lower bound. For q = 32 it is 4.4. ∎

## 3. Computational verification (all runs single-threaded)

| check | implementation | range | result |
|---|---|---|---|
| sym.py vs brute interpolation | `selftest.py` | m = 5, 7, random sparse A, L | coefficients, Z identical |
| family, every d ∈ F_q^* | `symcheck.py` (symbolic, q-free) | m = 5, 7, 9, 11, 13 | 31/127/511/2047/8191 agree; hits = N(m) |
| family, sampled d (40 admissible + 40 not) | `symcheck.py` | m = 15, 17, …, 31 | 80/80 agree for each m |
| function-level, every d | `brute.c` (full evaluation, interpolation, fail-closed re-evaluation, p' 2-to-1, ρ, μ by Hasse coefficient, Λ at all points) | m = 5, 7, 9, 11, 13 | all agree; ρ = d^{−4}, ε = (1+d)^2 confirmed |
| APN by full DDT | `brute.c … 1` | m = 5, 7, 9 all d; m = 11, 10 d | APN everywhere (as theory says) |
| function-level, sampled d | `brute.c sample` | m = 15 (100+100), 17 (25+25), 19 (6+6), 21 (2+2) | all agree (m = 21: 4/4, 2 hits) |
| independent invariants | `../inv.py` (read-only) on term files `terms/` | m = 5 (d = 2, 4, 9), 7 (12, 26, 28), 9 (2, 4), 11 (2) | ρ matches, μ = 0, Z = [] |
| N(m), K_m, Weil | `count.c` | m = 5 … 21 | N = (q−3+K)/4 and |K| ≤ 2√q hold |

The field polynomials are those in `polys.txt`. For m ≤ 13 they are identical to inv.py/rsearch.c (37, 131, 529,
2053, 8219). The integer d is the polynomial-basis bit vector (bit i ↔ t^i).

N(m) for m = 5…21 is 10, 28, 126, 528, 2002, 8260, 32742, 130872, 524986.

## 4. Gaps and remarks (honest)
- The proof is complete for all odd m ≥ 5. The only cited theorem is Weil's Kloosterman bound, and only existence
  of d depends on it. No closed-form d valid for all m is given. d = t works for the polynomials used at
  m = 5, 9, 11, but that depends on the modulus.
- m = 3 is not covered: m − 2 = 1 collides with a_1. The problem asks for m ≥ 5.
- The family is not sparse: all m coefficients of A_d are nonzero, so p_d has Θ(m^2) terms (12 terms of degree 24
  for m = 5). It is uniform and explicit, though.
- Side observation, not proved: inv.py reports that the natural lift often has A_F zero-free (A_zero = 0), for
  example m = 7 (all three tested d) and m = 9. It also has A_zero = 4 for m = 5 with d = 2 and for m = 11 with d = 2.
  When A_F is zero-free, the exceptional rows are predicted to be flat at q at all k. This was not studied further.
- Negative structural fact found along the way, with proof: if all coefficients of p lie in F_2, then ρ = 1 and
  Λ ≡ const + M with const = p(1) + p(0) + ε = 0 lying in Im M, so Z ≠ ∅. This is why d ∉ F_2 is forced.

## 5. Files
- `sym.py`: field arithmetic and symbolic invariants (ε, K, ρ, μ, Λ via linear algebra; no q-loops).
- `selftest.py`: cross-check of sym.py against interpolation.
- `symcheck.py`: verification of the theorem with sym.py → `out/symcheck_*.json`.
- `brute.c`: independent function-level verifier → `out/brute_m*_*.jsonl` (last line SUMMARY).
- `count.c`: N(m), K_m → `out/count_valid_d.jsonl`.
- `mkterms.py`, `terms/`: inv.py-format term files → `out/terms_index.json`, `out/invpy_check.txt`.
- `explore*.py`, `quick.py`: exploratory searches that led to the family (explore3: 3-term A has μ ≠ 0
  throughout; explore4: the μ = 0 sub-family x + x^2 + c x^{2^{m−2}} + x^{2^{m−1}}).
