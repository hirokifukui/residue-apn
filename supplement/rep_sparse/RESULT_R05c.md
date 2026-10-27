# RESULT_R05c (research note; named RESULT_R06 during the work) — Sparse representatives with μ = 0 and Z = ∅ for every odd m ≥ 5, and low-cost optimal lifts

Claude, 2026-10-26. Work directory `/home/claude/w/research/sparse_r06/`. Originals in `/home/claude/w/r07/` were only read.
Notation as in `tex/apn2_full.tex`: (H), ρ, ε, K, μ, Λ, Z, A_F, R_k = GR(2^k, m), Δ_exc. Indices of linearized
coefficients are taken mod m; σ is the Frobenius x ↦ x², T_0 = {t : Tr t = 0}, [u] is any lift of u ∈ F_q to R_k.

## 0. Status in one paragraph

Open problem (1) of §10 is settled for the representative part with a **16-term family** (12 terms for m = 5):

  B_c(x) = x^{q/4} + x^{q/2} + x + x² + c·x⁴,  p_c = reduced polynomial of B_c(x)³.

*Proved for all odd m ≥ 5:* (Theorem 1) whenever c ∉ F_2 and B_c is injective, p_c satisfies (H) with ε = 1, ρ = B_c^{-1}(1),
μ = 0 and Z = ∅; (Theorem 2) such c exist for every odd m ≥ 5. Theorem 1 is elementary. Theorem 2 uses an elementary
counting identity, the Aubry–Perret form of the Weil bound for one explicit plane curve of degree 14 (for m ≥ 15), one finite
point count over F_{2^17} (to show the curve has an absolutely irreducible component defined over F_2), and an exhaustive
computation for m = 5, …, 13. No closed-form c valid for all m is given (as in repfamily); c is found by a rank test.
*Lifts:* (Lemma A, general) for every lift whose exponents have binary weight ≤ 2, A_F is affine with a linear part that does
not depend on the lift. Consequences: (Corollary G) every (H)-representative with μ = 0 has an optimal lift with the same
monomials and degree as its natural lift, obtained by changing the 2-adic digit of one coefficient, at most half of the digit
choices fail, and the extra cost is 0 multiplications if that coefficient is outside F_2 (≤ 1 otherwise); for p_c the cost is
0. (Theorem 4) an explicit, certified lift F^♮ of p_c with one trace bit as certificate, at the price of 3 ring
multiplications and 3 additions (2 and 2 for m = 5), which is optimal at every level k ≥ 3: every exceptional row consists of
q^{k-1} entries equal to q. All statements were checked by independent computations (Section 5): 0 mismatches.

## 1. The family

For c ∈ F_q put a_{-2} = a_{-1} = a_0 = a_1 = 1, a_2 = c (all other a_i = 0), so B_c = Σ a_i x^{2^i}. Since m ≥ 5, the
positions −2, −1, 0, 1, 2 are distinct mod m. By §2.1 of RESULT_R05b (and the proof of Theorem repfamily), the reduced
polynomial of x ↦ B(x)³ has coefficients c_{uv} = a_{u-1}²a_v + a_{v-1}²a_u at X^{2^u+2^v} (u ≠ v) and l_w = a_{w-2}²a_{w-1}
at X^{2^w}. For m ≥ 7 this gives exactly 16 monomials (q = 2^m):

  p_c = X + X² + X⁴ + c X⁸ + (1+c)(X⁵ + X⁶) + c²(X⁹ + X¹⁰) + c³ X¹²
        + X^{1+q/4} + X^{2+q/4} + X^{4+q/4} + c² X^{8+q/4} + (1+c) X^{4+q/2} + c² X^{8+q/2} + X^{3q/4}.

For m = 5 the positions 3 ≡ −2 and 2 ≡ −3 collide and p_c has 12 monomials (listed in `out/check_family_5_7_9.json`
via `family.py`; e.g. X⁹ has coefficient 1 + c²). Degree 3q/4 in all cases. All coefficients lie in {1, c, c², c³, 1+c, 1+c², 1+c³}.

## 2. Theorem 1 (invariants)

**Theorem 1.** Let m ≥ 5 be odd, c ∈ F_q \ F_2, and suppose B_c is injective. Then p_c is a reduced quadratic APN permutation
satisfying (H) with

  ε = 1,  K(y) = B_c(y) + B_c(y)² (= (1+c)y⁴ + c²y⁸ + y^{q/4} for m ≥ 7),  K(F_q) = T_0,  ρ = B_c^{-1}(1) ≠ 1,
  μ = 0,  Λ(a) = (1+ρ)(w² + w + 1) with w = B_c(a),  Z = ∅.

Within the family the hypotheses are necessary: if B_c is not injective p_c is not a permutation; c = 0 gives a
non-injective B_0; c = 1 gives coefficients in F_2, and then (if B_1 is injective, i.e. 5 ∤ m) ρ = 1 and Λ ≡ 0, Z = F_q.

*Proof.* General formulas (RESULT_R05b §2.1, valid when a_0 a_{-1} ≠ 0): with r = a_{-1}²/a_0, ε = a_{-2}²a_{-1},
K(y) = a_{-1}²B(y) + a_0B(y)² = a_0 w(w + r) (w = B(y)), ker K = B^{-1}{0, r}, K(F_q) = a_0r²T_0, μ = a_0²r + a_1r²,
Λ(a) = (r + a_0ρ)(w² + rw) + r³ + ρε. Here r = 1, so ker K = {0, ρ} with ρ = B_c^{-1}(1) (B_c bijective), K(F_q) = T_0,
ε = 1 ∉ T_0 because Tr 1 = 1 for odd m: (H) holds. μ = 1 + 1 = 0. B_c(1) = 1+1+1+1+c = c ≠ 1, so ρ ≠ 1, and
Λ(a) = (1+ρ)(w² + w) + 1 + ρ = (1+ρ)(w² + w + 1). Since m is odd, w² + w + 1 has no root in F_q (its roots generate F_4),
so Λ has no zero. APN and permutation: x³ is an APN permutation for odd m and B_c is an F_2-linear bijection. The value
of K for m ≥ 7: B + B² has coefficients a_v + a_{v-1}², nonzero only at v = 2 (1+c), 3 (c²), −2 (1). For c = 1 the
same computation gives ρ = 1 = r = a_0ρ and Λ ≡ r³ + ρε = 0. ∎

Remark (mechanism). The four coefficients a_{-2..1} = (1,1,1,1) are the only ones that enter ε, r, μ and the Λ-test; they
force μ = 0 and ε = a_0r², and ε = a_0r² makes the Λ-test independent of ρ: Tr((r³+ρε)/((r+a_0ρ)r²)) = Tr(1) = 1 as soon
as r ≠ a_0ρ. This is why ρ never has to be known explicitly; the free coefficient c only has to make B_c injective
and B_c(1) ≠ 1.

## 3. Theorem 2 (existence of the parameter for every odd m ≥ 5)

Let C_m = {c ∈ F_q \ F_2 : B_c injective}.

**Theorem 2.** C_m ≠ ∅ for every odd m ≥ 5. More precisely |C_m| = 15, 42, 126, 506, 2496 for m = 5, 7, 9, 11, 13, and
|C_m| ≥ 2 for every odd m ≥ 15.

*Proof.* (a) *Kernels.* For x ≠ 0 put y = x^{1/4} (= x^{q/4}), z = 1/y. Then B_c(x) = y + y² + y⁴ + y⁸ + c y^{16}, so
B_c(x) = 0 ⇔ c = h(z), h(z) := z^{15} + z^{14} + z^{12} + z^8. Every x ≠ 0 lies in ker B_c for exactly one c.

(b) *Counting identity.* Summing over c ∈ F_q: Σ_c (|ker B_c| − 1) = q − 1. Let b be the number of c with ker B_c ≠ 0. Then
q − 1 = b + Σ_{ker≠0}(|ker B_c| − 2), so

  #{c ∈ F_q : B_c injective} = q − b = 1 + Σ_{c : ker B_c ≠ 0} (|ker B_c| − 2).

Kernel sizes are powers of 2, so the number of injective c is odd, and it is ≥ 3 as soon as one c has dim ker B_c ≥ 2.
c = 0 is never injective (B_0(1) = 0). Hence C_m ≠ ∅ if B_1 is not injective, and |C_m| ≥ 2 if some c has
dim ker B_c ≥ 2.

(c) *The curve.* dim ker B_c ≥ 2 for some c ⇔ there are z ≠ w in F_q^* with h(z) = h(w) (then z^{-4}, w^{-4} are distinct
nonzero kernel elements of B_{h(z)}). Let Q(z, w) = (h(z) + h(w))/(z + w) ∈ F_2[z, w], of total degree 14. Q(z, z) = h'(z) = z^{14}
and Q(0, w) = w^{14} + w^{13} + w^{11} + w^7, so none of the lines z = w, z = 0, w = 0 is a component of Q = 0.

(d) *An absolutely irreducible component over F_2.* Over F_{2^17} the affine curve Q = 0 has exactly 125769 points
(Σ_c N_c(N_c − 1) + 1 with N_c = #h^{-1}(c); computed by two independent programs, `kercount.c` and `curve_count.py`). Suppose
no absolutely irreducible component of Q were defined over F_2. Frobenius over F_2 permutes the ≤ 14 components; a component
is defined over F_{2^j} exactly when its orbit length divides j, and orbit lengths are ≤ 14 < 17 with 17 prime, so no
component would be defined over F_{2^17}. Every F_{2^17}-point would then lie on a component X and on its conjugate
Frob^{17}(X) ≠ X, and Bézout gives at most Σ_{i<j} d_i d_j ≤ 14²/2 = 98 points. Since 125769 > 98, Q has an absolutely
irreducible component X defined over F_2, of degree d ≤ 14.

(e) *Weil bound.* For odd m ≥ 15 (q ≥ 2^15), the Aubry–Perret bound for the projective closure X̄ (absolutely irreducible
plane curve of degree d over F_q; Y. Aubry, M. Perret, *A Weil theorem for singular curves*, in Arithmetic, Geometry and
Coding Theory, de Gruyter 1996) gives #X̄(F_q) ≥ q + 1 − (d−1)(d−2)√q ≥ q + 1 − 156√q. Removing ≤ d points at infinity and
≤ 3d affine points on the three lines of (c) leaves ≥ q + 1 − 156√q − 56 > 0 points (at q = 2^15: ≥ 4473). Such a point gives
c with dim ker B_c ≥ 2, hence |C_m| ≥ 2 by (b).

(f) *m ≤ 13.* Exhaustive computation (rank test and the fibre count of h agree): |C_m| = 15, 42, 126, 506, 2496. ∎

Additional data (`out/kercount.jsonl`; #{c : B_c injective}, which includes c = 1 when 5 ∤ m): m = 15: 9595, 17: 37843,
19: 151925, 21: 605179, 23: 2425029. The identity of (b) was checked numerically for m = 5, …, 23. Heuristically
|C_m| ≈ 0.29 q.

Dependencies of Theorem 2, stated plainly: the Aubry–Perret bound (a published Weil-type theorem), the integer 125769
(a finite computation), and the exhaustive computation for m ≤ 13. Theorem 1 and everything in Section 4 are elementary given
the theorems of the paper.

## 4. Lifts

### 4.1 Lemma A (general; the linear part of A_F does not depend on the lift)

**Lemma A.** Let p satisfy (H), with coefficients c_{uv} (at X^{2^u+2^v}, 0 ≤ u < v ≤ m−1), and let F be any lift of p all of
whose exponents have binary weight ≤ 2 (0, 2^w or 2^u + 2^v; exponents ≥ q allowed, their coefficients are then even). Then

  A_F(a) = A_F(0) + L_p(a),  L_p(a) = Σ_{v≥1} c_{0v}(aρ)^{2^{v-1}} + Σ_{v≥2} c_{1v}(aρ^{2^v} + ρa^{2^v})
                                    = K(√(aρ)) + ρK_1(a) + μa,

where K_1(y) = Σ_{v≠1} c_{1v}y^{2^v}. L_p is F_2-linear and L_p(ρ) = 0.

*Proof.* A_F(a) is the residue of (F'(x+τ) − F'(x))/2 with x̄ = a, τ̄ = ρ (Lemma A of the paper: independent of choices).
Take one monomial f X^e. (i) e = 2^u + 2^v with u ≥ 2, or e = 2^w with w ≥ 2: e ≡ 0 (mod 4), so the term of
(F'(x+τ) − F'(x))/2 is ≡ 0 (mod 2). (ii) e = 2: the term is fτ, a constant. e = 1, e = 0: no contribution.
(iii) e = 2 + 2^v (v ≥ 2): the term is (1 + 2^{v-1}) f [(x+τ)^{1+2^v} − x^{1+2^v}], with residue
f̄(aρ^{2^v} + ρa^{2^v} + ρ^{1+2^v}). (iv) e = 1 + 2^v (v ≥ 1): write (x+τ)^{2^v} = x^{2^v} + τ^{2^v} + 2D_v; by induction on v
(squaring kills 4-multiples) D_v ≡ (xτ)^{2^{v-1}} (mod 2). The term is (1+2^v) f τ^{2^v} + 2(1+2^v) f D_v; the second part
contributes f̄ (aρ)^{2^{v-1}} after division by 2, the first part does not depend on x. The sum of all x-independent parts lies
in 2R_k (everything else does and the total does), so it contributes a constant. Collecting, A_F(a) = const + Σ_{v≥1} c_{0v}
(aρ)^{2^{v-1}} + Σ_{v≥2} c_{1v}(aρ^{2^v} + ρa^{2^v}) (monomials with e ≥ q have f̄ = 0). For the second form: Σ_{v≥1} c_{0v}y^{2^v}
= K(y), and Σ_{v≥2}c_{1v}y^{2^v} = K_1(y) − c_{10}y, so the second sum is a(K_1(ρ) − c_{10}ρ) + ρ(K_1(a) − c_{10}a) = aμ + ρK_1(a)
(μ = K_1(ρ) by definition of μ). L_p(ρ) = K(ρ) + ρμ + μρ = 0. ∎

For p = B³ with a_{-1} = a_0 = a_1 = 1 one has c_{10} = a_0³ + a_{-1}²a_1 = 0 and K_1 = a_0²B + a_1B² = K, so for p_c:

  L_{p_c}(a) = K(√(aρ)) + ρK(a).                                                     (4.1)

### 4.2 Corollary G (zero-cost optimal lifts for every μ = 0 representative)

**Corollary G.** Let p satisfy (H) with μ = 0, let F be a lift as in Lemma A (e.g. the natural lift) and j ≥ 1 with
c_{0j} ≠ 0 (exists, since K ≠ 0). For u ∈ R_k let F_u be F with the coefficient f of X^{1+2^j} replaced by f + 2u. Then
A_{F_u} = A_F + ūρ^{2^j}, and F_u is optimal (Δ_exc = minimax value; for Z = ∅ every exceptional row is q^{k-1} entries equal
to q) at every level k ≥ 3 iff ūρ^{2^j} ∉ A_F(F_q). Since A_F(F_q) = A_F(0) + L_p(F_q) has at most q/2 elements, at least half of
the residues ū work. F_u has the same monomials and degree as F; if c_{0j} ∉ F_2, evaluating F_u costs no operation beyond F.

*Proof.* Prop. Acontrol(i) with H = uX^{1+2^j}: the residue of H' is ūa^{2^j}, whose ρ-difference is the constant ūρ^{2^j}.
Lemma A gives the image. Optimality: Theorems minimizers (μ = 0: optimal iff A_F has no zero, k = 3 and k ≥ 4), spectrum (1)
and Theorem CL / Corollary CL2 for compatibility across levels. ∎

For p_c take j = 2 (coefficient 1 + c ∉ F_2): **an optimal lift of p_c with exactly the 16 monomials of p_c and zero extra
multiplications always exists**; ū is found by linear algebra (A_F(F_q) is an affine subspace). Computed: the fraction of good
ū is ≥ 1/2 for every tested c (minimum exactly 1/2); the natural lift itself (ū = 0) is already optimal for 13/15 (m = 5),
28/42 (m = 7), 83/126 (m = 9), 7/10 and 3/6 sampled c (m = 11, 13). The choice of ū is not given by a closed formula.

*Remark on P_{m,r} (r ≥ 5, μ = 0).* There ρ = 1 and, by the paper's identities I3–I4, A_nat = L + L² takes values in T_0, while
F^♯ = F + 2X³ has A = L + L² + 1 (the constant shift ρ² = 1). By Corollary G, replacing the coefficient 1 of *any* monomial
X^{1+2^j} (j ≥ 1) of the natural lift by 3 produces the same shift ρ^{2^j} = 1, hence the same A and the same optimality, with the
same support and degree, at the price of two additions (3y = y + y + y) and no multiplication, one multiplication less than F^♯.
Checked for P_{7,5}: coefficient of X⁹ or of X³³ changed to 3 gives A zero-free (natural lift: 2 zeros). Not claimed for r = 3
(μ ≠ 0 there; the k ≥ 4 criterion also involves χ_F).

### 4.3 Theorem 4 (explicit certified lift of p_c)

**Theorem 4.** Let c ∈ C_m, ρ = B_c^{-1}(1), and F any lift of p_c as in Lemma A (e.g. the natural lift). Put

  F^♭ = F + 2[(1+c)ρ^{-7}] X^{13} + 2[ρ^{-7}] X^{9+q/4}   (m ≥ 7),   F^♭ = F + 2[(1+c)ρ^{-7}] X^{13}   (m = 5),
  κ = A_F(0) + (1+c)ρ⁵ + [m ≥ 7]·ρ^{1+q/4},  ε = 1 + Tr(κ) ∈ {0, 1},

and let F^♮ be F^♭ with the coefficient f_5 of X⁵ replaced by f_5 + 2ε[ρ^{-4}] (no new monomial). Then for every k ≥ 3

  A_{F^♮}(a) = κ + ε + K(√(aρ)),  which has no zero,

so F^♮ is optimal at every level: every exceptional row of F^♮ consists of q^{k-1} entries equal to q (and zeros), every
ordinary unit row has entries ≤ 2, Δ_unit(F^♮) = q = the minimax value for (μ = 0, Z = ∅), the integer coefficients define a
compatible family optimal at all levels, and (Theorem layers, s = 0) the penultimate layer is flat at q^{k-1} and the k = 3
middle layer is optimal. deg F^♮ = 3q/4 (13 and 9 + q/4 are < 3q/4).

*Proof.* Let H = [(1+c)ρ^{-7}]X^{13} + [ρ^{-7}]X^{9+q/4} (m ≥ 7). The residue of H' is h(a) = ρ^{-7}((1+c)a^{12} + a^{8+q/4})
(13 and 9 + q/4 are odd). For a Dembowski–Ostrom monomial, (a+ρ)^{2^i+2^j} + a^{2^i+2^j} = a^{2^i}ρ^{2^j} + ρ^{2^i}a^{2^j} + ρ^{2^i+2^j}, so

  D_ρh(a) = (1+c)ρ a⁴ + ρ^{-7}((1+c)ρ⁴ + ρ^{q/4}) a⁸ + ρ a^{q/4} + h(ρ).

K(ρ) = 0 reads (1+c)ρ⁴ + c²ρ⁸ + ρ^{q/4} = 0, so the a⁸ coefficient is c²ρ and D_ρh(a) = ρK(a) + h(ρ), with
h(ρ) = (1+c)ρ⁵ + ρ^{1+q/4}. (m = 5: h = (1+c)ρ^{-7}a^{12}, K(y) = (1+c)y⁴ + (1+c²)y⁸, and K(ρ) = 0 gives D_ρh = ρK(a) + (1+c)ρ⁵.)
By Prop. Acontrol(i), Lemma A and (4.1): A_{F^♭}(a) = A_F(0) + K(√(aρ)) + ρK(a) + ρK(a) + h(ρ) = κ + K(√(aρ)). The X⁵ change is
2ε[ρ^{-4}]X⁵, which adds the constant ε·ρ^{-4}·ρ⁴ = ε (Corollary G with j = 2). The map a ↦ K(√(aρ)) has image K(F_q) = T_0, and
Tr(κ + ε) = Tr κ + ε = 1, so κ + ε ∉ T_0 and A_{F^♮} has no zero. The rest is Theorems minimizers, spectrum (1) with μ = 0,
|Z| = 0 (n_q = q·q^{k-2}, all other multiplicities 0), Lemma ordinary, Theorem CL/Corollary CL2, Theorem layers. Exponents
of F^♮ are fixed integers and its coefficient digits are the same at every level, so its reductions are compatible. ∎

### 4.4 Operation count

Cost is counted as in Theorem oneterm: ring operations on top of the evaluation of the natural lift F, whose schedule computes
x^{2^i} by m−1 squarings and each Dembowski–Ostrom monomial as one product of two such powers times its coefficient (in
particular x⁹ = x·x⁸, since X⁹ ∈ supp p_c with coefficient c² for m ≥ 7 and 1 + c² for m = 5).

| lift | extra multiplications | extra additions | new monomials | degree |
|---|---|---|---|---|
| F_u of Corollary G (j = 2) | 0 | 0 | 0 | 3q/4 |
| F^♮, m ≥ 7: t = [(1+c)ρ^{-7}]·x⁴ + [ρ^{-7}]·x^{q/4}; s = x⁹·t; add s + s | 3 | 3 | 2 | 3q/4 |
| F^♮, m = 5: s = x⁹·([(1+c)ρ^{-7}]·x⁴); add s + s | 2 | 2 | 1 | 3q/4 |

(The X⁵-coefficient change in F^♮ costs nothing: the coefficient 1 + c is a general ring constant in F as well. If the natural
schedule forms f_5·x⁴ before multiplying by x, then H = [ρ^{-7}]·x⁹·(f_5x⁴ + x^{q/4}) costs 2 multiplications for m ≥ 7,
because only residues of coefficients of H matter.) Compared with F^♯ for P_{m,r} (1 multiplication, 2 additions), F^♮ costs
two more multiplications, but carries a closed-form certificate. F_u costs nothing, but its digit ū is found by linear
algebra.

## 5. Verification (all runs on this machine, 2 shared cores; 0 mismatches)

| # | check | tool (independent of …) | range | result |
|---|---|---|---|---|
| 1 | Theorem 1 vs symbolic invariants, every c ∈ F_q | `check_family.py` (sym.py) | m = 5, 7, 9, 11, 13 | 32/32, 128/128, 512/512, 2048/2048, 8192/8192 agree; admissible c: 15, 42, 126, 506, 2496; ρ = B^{-1}(1), ε = 1, μ = 0, Z = ∅ for all; 16 terms (12 at m = 5), degree 3q/4 |
| 2 | Theorem 1, sampled | `check_family_sample.py` | m = 15, 17, …, 31, 20 injective c each | 180/180 agree, 16 terms |
| 3 | Theorem 1, function level (evaluation at all points, fail-closed interpolation, p′ 2-to-1, ρ, μ by Hasse coefficient, Λ at all points) | `brute_sparse.c` (adapted from rep_family/brute.c; independent of sym.py) | m = 5, 7, 9 all c with full DDT (APN); m = 11, 13 all c; m = 15 (40 c), 17 (12), 19 (4) random | all agree: 32, 128, 512, 2048, 8192, 40, 12, 4; hits 15, 42, 126, 506, 2496, 14, 2, 2 |
| 4 | counting identity of Thm 2(b), #injective c, dim-≥2 kernels | `kercount.c` | m = 5, …, 23 | identity holds for all; N_{≥2} ≥ 1 for all; c = 1 injective iff 5 ∤ m |
| 5 | curve point count over F_{2^17} (Thm 2(d)) | `kercount.c`, `curve_count.py` (two implementations) | m = 17 (also 19, 21, 23 with kercount) | 125769 (both) > 98 |
| 6 | Lemma A (A_F affine, formula for L_p), pointwise over F_q | `gr aset` (brute force in R_3) + `lifts.py`, `check_Alemma.py` | natural lifts of p_c: m = 5 (15 c), 7 (42), 9 (126), 11 (10), 13 (6); 17 lifts of other representatives (repfamily p_d, P_{5,3}, P_{7,3}, P_{7,5}, F^♯'s, rep5, rep7, c1) | 199/199 + 17/17 OK; 2 lifts with weight-3 exponents correctly reported as out of scope |
| 7 | Theorem 4: A_{F^♮} = κ + ε + K(√(aρ)) pointwise, A zero-free | `gr aset` | same c as #6 | formula 199/199, zero-free 199/199; ε = 1 in 8/15, 22/42, 62/126, 6/10, 4/6 |
| 8 | Corollary G: good fraction of ū, brute check of chosen ū | `zerocost.py` + `gr aset` | m = 5 (15 c), 7 (42), 9 (30) | min fraction 0.5; 30/30, 84/84, 60/60 zero-free |
| 9 | full exceptional rows, k = 3, F^♮ | `gr rows` (brute force over R_3, all x) | m = 5: all 15 c × 1024 rows | 15360/15360 MATCH (each row: 1024 entries 32), max 32 = q |
| 10 | full exceptional rows, k = 3, F^♮ | `gr rows` | m = 7, c = 9: all 16384 rows | 16384/16384 MATCH (each row: 16384 entries 128), max 128 = q |
| 11 | full exceptional rows, k = 3, F^♮ | `gr rows` | m = 7, c = 28 (ε = 1, natural lift has 4 zeros of A): all 16384 rows | 16384/16384 MATCH, max 128; natural lift: 200/200 sampled rows MISMATCH with max q² |
| 12 | full exceptional rows, k = 4, F^♮ | `gr rows` | m = 5, c = 3: all 32768 rows | 32768/32768 MATCH (32768 entries 32), max 32 |
| 13 | sampled exceptional rows, k = 4, F^♮ | `gr rows` | m = 5, 256 rows for each of 15 c | 3840/3840 MATCH, max 32 |
| 14 | sampled exceptional rows, k = 4, F^♮ (table by exact Taylor expansion at Teichmüller points; checked = direct evaluation at m = 5, k = 3, 4: 0 differences) | `gr rowsT` | m = 7, c = 9, 16 rows | 16/16 MATCH, max 128 |
| 15 | ordinary unit rows, k = 3, F^♮ | `gr ord` | m = 5: 300 random rows × 15 c | 4500/4500 entries ≤ 2 |
| 16 | negative controls: natural lifts with zeros of A (m = 5, c = 15, 17); Corollary G with a bad ū (c = 15, u = 1; c = 17, u = 2) | `gr rows` | all 1024 rows each | MISMATCH in 1024/1024 rows each, max entry q² = 1024, exactly as predicted (classes with A = 0 give q² solutions); natural lifts with A zero-free: 13 × 1024 MATCH; good ū: 2 × 1024 MATCH |

### 5.1 Long runs (filled from `out/rows/`)

| run | rows | MATCH | MISMATCH | max entry |
|---|---|---|---|---|
| m = 7, c = 9, F^♮, k = 3, all exceptional rows (2 halves) | 16384 | 16384 | 0 | 128 = q |
| m = 7, c = 28, F^♮ (ε = 1), k = 3, all exceptional rows (2 halves) | 16384 | 16384 | 0 | 128 = q |
| m = 7, c = 28, natural lift (A has 4 zeros), k = 3, 200 random rows (negative control) | 200 | 0 | 200 | 16384 = q² (as predicted) |
| m = 7, c = 28, F^♮, k = 3, 200 random ordinary unit rows | 200 | 200 | 0 | 2 |
| m = 7, c = 9, F^♮, k = 4, 16 random exceptional rows (Taylor table, |R_4| = 2^28) | 16 | 16 | 0 | 128 = q (each row: 2097152 = q³ entries equal to q) |

Totals for F^♮ exceptional rows: k = 3: 15360 (m = 5) + 32768 (m = 7) = 48128 MATCH; k = 4: 32768 + 3840 (m = 5) + 16 (m = 7)
= 36624 MATCH; 0 MISMATCH. Ordinary rows: 4700, all entries ≤ 2. Every predicted negative control mismatched.

## 6. What is proved and what is computed

- Proved for all odd m ≥ 5: Theorem 1; Theorem 2 (with Aubry–Perret and the stated finite computations); Lemma A;
  Corollary G (existence of a zero-cost optimal lift; its digit is computed, not given in closed form); Theorem 4 (explicit lift,
  closed-form certificate: one trace bit computed from A_F(0)).
- Optimality statements for the lifts rest on the paper's Theorems minimizers, spectrum, CL/CL2, layers and Lemma ordinary;
  nothing new is assumed about lifts.
- Computed only: the exact sizes |C_m| (m ≤ 23), the proportion of c for which the natural lift is already optimal, and the
  row verifications of Section 5.
- Not done: a closed-form c valid for all m (impossible in this generality: F_q has no distinguished non-F_2 element across
  all odd m; repfamily has the same feature); an explicit description of which ū in Corollary G work; k ≥ 5 rows (covered by the
  mod-8 certification theorem, not recomputed).
- Minor correction to the paper's text (§10, after Theorem repfamily): "p_d is not sparse (p_d has of the order of m² terms)".
  From c_{uv} = a_{u-1}²a_{v-1}²(κ_u + κ_v) with κ_u = a_u/a_{u-1}² (κ_u = 1 except at u = m−2, m−1) one gets c_{uv} ≠ 0 only if u or
  v ∈ {m−2, m−1}, so p_d has 3m − 3 monomials (2m − 3 Dembowski–Ostrom terms and m linear terms; computed for m = 5, …, 17),
  not Θ(m²). It is still not sparse.

## 7. Files and reproduction

Sources (all in this directory): `sym.py` (copied from rep_family), `family.py`, `check_family.py`, `check_family_sample.py`,
`brute_sparse.c`, `kercount.c`, `curve_count.py`, `gr.c`, `lifts.py`, `run_lifts.py`, `zerocost.py`, `check_Alemma.py`,
`run_rows_m5.sh`, `polys.txt` (field polynomials; m ≤ 13 identical to inv.py/rsearch.c), `inv.py` (copy, unused by the
pipeline). Exploratory searches that led to the family: `explore/` (not needed for reproduction). Data: `out/`, `terms/`
(lift term files in inv.py format; digits mod 2^k).

```sh
cd /home/claude/w/research/sparse_r06
gcc -O2 -o brute_sparse brute_sparse.c; gcc -O2 -o kercount kercount.c; gcc -O3 -march=native -o gr gr.c
python3 check_family.py 5 7 9; python3 check_family.py 11; python3 check_family.py 13     # Thm 1, all c
python3 check_family_sample.py                                                           # Thm 1, m = 15..31
./brute_sparse 7 131 all 1; ./brute_sparse 13 8219 all 0; ./brute_sparse 17 131081 sample 12
for m in 5 7 9 11 13 15 17 19 21 23; do ./kercount $m $(awk -v m=$m '$1==m{print $2}' polys.txt); done
python3 curve_count.py                                                                   # 125769 points over F_{2^17}
python3 run_lifts.py 5; python3 run_lifts.py 7; python3 run_lifts.py 9; python3 run_lifts.py 11 10; python3 run_lifts.py 13 6
python3 zerocost.py 5; python3 zerocost.py 7; python3 zerocost.py 9 30
./run_rows_m5.sh                                                                        # m = 5 rows (k = 3 all, k = 4)
./gr rows 7 131 3 terms/m7_c9_flat.txt 48 -1 0 0 8192; ./gr rows 7 131 3 terms/m7_c9_flat.txt 48 -1 0 8192 16384
./gr rows 7 131 3 terms/m7_c28_flat.txt 110 -1 0 0 8192; ./gr rows 7 131 3 terms/m7_c28_flat.txt 110 -1 0 8192 16384
./gr rowsT 7 131 4 terms/m7_c9_flat.txt 48 16 7
```

`gr rows m poly k terms rho [nrows seed [r0 r1]]`: nrows = 0 → all q^{k-1} exceptional rows; nrows = −1 → rows r0 ≤ r < r1;
each row is compared with "q^{k-1} entries equal to q". Field elements are integers in the polynomial basis (bit i ↔ t^i).
Runtime: m = 7, k = 3, all rows ≈ 6 min wall per half on the shared machine.
