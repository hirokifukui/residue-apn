import ResidueAPN.TheoremA

/-!
# Theorem 4.1 (B) of paper_R5 — the algebraic core

`s = m - r`, `ℓ = 2^(r-2)`, `g = X^(2^s) + X + 1`.

Formal here (any field `K` of characteristic two for root statements; `AlgebraicClosure (ZMod 2)`
for the count and for `gcd(g, E) = 1` over `𝔽₂`):
* (1) `P' = g^ℓ` and `P + 1 = g^ℓ E` (`derivative_polP_eq_pow`, `polP_add_one_eq_pow`);
* (2) `g` is separable; every root `α` satisfies `α^(2^(2s)) = α`, `α^(2^s) ≠ α`, `α^(2^m) ≠ α`
  (i.e. `α ∈ 𝔽_{2^{2s}} \ (𝔽_{2^s} ∪ 𝔽_q)`); `g` has exactly `2^s` roots in `\bar 𝔽₂`;
* (3) `gcd(g, E) = 1` in `𝔽₂[X]` (`isCoprime_polG_polE`);
* consequences: at a root `α` of `g`, `P(α) = 1`, and the multiplicity of `α` as a root of `P + 1`
  and of `P'` is exactly `ℓ` (`e_α = d_α = ℓ`); `P'` vanishes exactly at the roots of `g`.

Not formalized: the identification of `e_α`, `d_α` with ramification indices and different exponents
of the map `ℙ¹ → ℙ¹`, the point at infinity (`e_∞ = n`, `d_∞ = 5q/4 - 2` via Riemann–Hurwitz), and the
description of the fibre over `1`.
-/

namespace ResidueAPN

open Polynomial Finset

section Defs

variable (R : Type*) [CommRing R]

noncomputable def polG (s : ℕ) : R[X] := X ^ (2 ^ s) + X + 1

@[simp] theorem map_polG {S : Type*} [CommRing S] (f : R →+* S) (s : ℕ) :
    (polG R s).map f = polG S s := by simp [polG]

end Defs

section Identities

variable {R : Type*} [CommRing R] [CharP R 2]

/-- **Theorem 4.1(1), first half.** `g^ℓ = D`, hence `P' = g^ℓ`. -/
theorem polG_pow {m r : ℕ} (hr : 2 ≤ r) (hrm : r < m) :
    polG R (m - r) ^ (2 ^ (r - 2)) = polD R m r := by
  unfold polG polD polW polY
  rw [add_pow_char_pow (R := R[X]) _ _ 2 (r - 2), add_pow_char_pow (R := R[X]) _ _ 2 (r - 2), one_pow,
    ← pow_mul, ← pow_add, show m - r + (r - 2) = m - 2 by omega]
  ring

theorem derivative_polP_eq_pow {m r : ℕ} (hr : 3 ≤ r) (hrm : r < m) :
    derivative (polP R m r) = polG R (m - r) ^ (2 ^ (r - 2)) := by
  rw [polG_pow (by omega) hrm, derivative_polP hr (by omega)]

/-- **Theorem 4.1(1), second half.** `P + 1 = g^ℓ E`. -/
theorem polP_add_one_eq_pow {m r : ℕ} (hr : 2 ≤ r) (hrm : r < m) :
    polP R m r + 1 = polG R (m - r) ^ (2 ^ (r - 2)) * polE R m r := by
  rw [polG_pow hr hrm, polP_add_one (by omega)]

theorem derivative_polG {s : ℕ} (hs : 1 ≤ s) : derivative (polG R s) = 1 := by
  unfold polG
  rw [derivative_add, derivative_add, derivative_X_two_pow hs, derivative_X, derivative_one]
  ring

/-- **Theorem 4.1(2): `g` is separable.** -/
theorem separable_polG {s : ℕ} (hs : 1 ≤ s) : (polG R s).Separable := by
  rw [Polynomial.separable_def, derivative_polG hs]
  exact isCoprime_one_right

end Identities

section Roots

variable {K : Type*} [Field K] [CharP K 2]

theorem root_frob {s : ℕ} {α : K} (h : (polG K s).eval α = 0) : α ^ (2 ^ s) = α + 1 := by
  simp only [polG, eval_add, eval_pow, eval_X, eval_one] at h
  linear_combination h + (-α - 1) * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem root_frob_add {s : ℕ} {α : K} (h : (polG K s).eval α = 0) (j : ℕ) :
    α ^ (2 ^ (s + j)) = α ^ (2 ^ j) + 1 := by
  rw [pow_add, pow_mul, root_frob h, frob_add, one_pow]

/-- Roots of `g` lie in `𝔽_{2^{2s}}`. -/
theorem root_fixed_two_s {s : ℕ} {α : K} (h : (polG K s).eval α = 0) : α ^ (2 ^ (2 * s)) = α := by
  rw [two_mul, root_frob_add h, root_frob h]
  linear_combination (CharTwo.two_eq_zero : (2 : K) = 0)

/-- Roots of `g` are not in `𝔽_{2^s}`. -/
theorem root_not_fixed_s {s : ℕ} {α : K} (h : (polG K s).eval α = 0) : α ^ (2 ^ s) ≠ α := by
  rw [root_frob h]; intro h'
  exact one_ne_zero (by linear_combination h')

theorem polG_eval_zero_one {s : ℕ} : (polG K s).eval 0 = 1 ∧ (polG K s).eval 1 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · simp [polG]
  · simp only [polG, eval_add, eval_pow, eval_X, eval_one, one_pow]
    linear_combination h2

/-- If `gcd(2s, n) = 1`, roots of `g` are not fixed by `x ↦ x^(2^n)`; with `n = m` this is
`α ∉ 𝔽_q`. -/
theorem root_not_fixed_of_coprime {s n : ℕ} (hcop : Nat.Coprime (2 * s) n) {α : K}
    (h : (polG K s).eval α = 0) : α ^ (2 ^ n) ≠ α := by
  intro hn
  rcases eq_zero_or_one_of_fixed hcop (root_fixed_two_s h) hn with h0 | h1
  · rw [h0, polG_eval_zero_one.1] at h; exact one_ne_zero h
  · rw [h1, polG_eval_zero_one.2] at h; exact one_ne_zero h

/-- `T_r(x)^2 + T_r(x) = x^(2^r) + x` in any field of characteristic two. -/
theorem evalT_sq_add' (r : ℕ) (x : K) :
    (polT K r).eval x ^ 2 + (polT K r).eval x = x ^ (2 ^ r) + x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [polT, eval_finsetSum, eval_pow, eval_X]
  have hs := Finset.sum_range_succ' (fun i => x ^ 2 ^ i) r
  rw [Finset.sum_range_succ] at hs
  rw [show (∑ i ∈ range r, x ^ 2 ^ i) ^ 2 = ∑ i ∈ range r, x ^ 2 ^ (i + 1) by
    rw [show (2 : ℕ) = 2 ^ 1 by norm_num, frob_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← pow_mul, ← pow_succ]]
  simp only [pow_zero, pow_one] at hs
  linear_combination (-1 : K) * hs + (∑ i ∈ range r, x ^ 2 ^ i - x) * h2

/-- At a root of `g` (with `s = m - r`), `E(α) = 1 + T_r(α)`. -/
theorem evalE_at_root {m r : ℕ} (hr : 2 ≤ r) (hrm : r < m) {α : K}
    (h : (polG K (m - r)).eval α = 0) :
    (polE K m r).eval α = 1 + (polT K r).eval α := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hY : α ^ (2 ^ (m - 2)) = α ^ (2 ^ (r - 2)) + 1 := by
    rw [show m - 2 = (m - r) + (r - 2) by omega, root_frob_add h]
  have hZ : α ^ (2 ^ (m - 1)) = α ^ (2 ^ (r - 1)) + 1 := by
    rw [show m - 1 = (m - r) + (r - 1) by omega, root_frob_add h]
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  simp only [polE, polV, polY, polZ, polT, eval_add, eval_one, eval_finsetSum, eval_pow, eval_X]
  rw [hY, hZ, Finset.sum_range_succ, Finset.sum_range_succ, show k + 2 - 2 = k by omega,
    show k + 2 - 1 = k + 1 by omega]
  linear_combination (1 : K) * h2

/-- **Theorem 4.1(3) at the level of roots.** `g` and `E` have no common root (any char-2 field). -/
theorem evalE_ne_zero_at_root {m r : ℕ} (hr : 2 ≤ r) (hrm : r < m) (hrodd : Odd r)
    (hcop : Nat.Coprime r m) {α : K} (h : (polG K (m - r)).eval α = 0) :
    (polE K m r).eval α ≠ 0 := by
  rw [evalE_at_root hr hrm h]
  intro hE
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hT : (polT K r).eval α = 1 := by linear_combination hE + (-1 : K) * h2
  have hsq := evalT_sq_add' r α
  rw [hT] at hsq
  have hfix : α ^ (2 ^ r) = α := by linear_combination -hsq + (1 - α) * h2
  have hc : Nat.Coprime r (2 * (m - r)) :=
    Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hrodd) ((Nat.coprime_sub_self_right hrm.le).mpr hcop)
  rcases eq_zero_or_one_of_fixed hc hfix (root_fixed_two_s h) with h0 | h1
  · rw [h0, polG_eval_zero_one.1] at h; exact one_ne_zero h
  · rw [h1, polG_eval_zero_one.2] at h; exact one_ne_zero h

/-- `rootMultiplicity` of a power. -/
theorem rootMultiplicity_pow' {p : K[X]} (hp : p ≠ 0) (a : K) (n : ℕ) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ih]; ring

theorem polG_ne_zero {s : ℕ} (hs : 1 ≤ s) : polG K s ≠ 0 := by
  intro h; have := derivative_polG (R := K) hs; rw [h, derivative_zero] at this; exact zero_ne_one this

/-- **Ramification indices and different exponents (algebraic form).** At a root `α` of `g`:
`P(α) = 1`, `α` is a root of `P + 1` of multiplicity exactly `ℓ`, and of `P'` of multiplicity
exactly `ℓ`. -/
theorem multiplicity_at_root {m r : ℕ} (hr : 3 ≤ r) (hrm : r < m) (hrodd : Odd r)
    (hcop : Nat.Coprime r m) {α : K} (h : (polG K (m - r)).eval α = 0) :
    (polP K m r).eval α = 1 ∧
    rootMultiplicity α (polP K m r + 1) = 2 ^ (r - 2) ∧
    rootMultiplicity α (derivative (polP K m r)) = 2 ^ (r - 2) := by
  have hs : 1 ≤ m - r := by omega
  have hg0 := polG_ne_zero (K := K) hs
  have hE := evalE_ne_zero_at_root (K := K) (by omega) hrm hrodd hcop h
  have hE0 : polE K m r ≠ 0 := by intro h0; rw [h0, eval_zero] at hE; exact hE rfl
  have hmg : rootMultiplicity α (polG K (m - r)) = 1 := by
    apply le_antisymm (rootMultiplicity_le_one_of_separable (separable_polG hs) α)
    exact (rootMultiplicity_pos hg0).mpr h
  have hmE : rootMultiplicity α (polE K m r) = 0 := rootMultiplicity_eq_zero hE
  refine ⟨?_, ?_, ?_⟩
  · have e := congrArg (eval α) (polP_add_one_eq_pow (R := K) (by omega) hrm)
    simp only [eval_add, eval_one, eval_mul, eval_pow, h, zero_pow (pow_ne_zero _ two_ne_zero),
      zero_mul] at e
    linear_combination e + (-1 : K) * (CharTwo.two_eq_zero : (2 : K) = 0)
  · rw [polP_add_one_eq_pow (by omega) hrm,
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hg0) hE0), rootMultiplicity_pow' hg0, hmg, hmE]
    ring
  · rw [derivative_polP_eq_pow hr hrm, rootMultiplicity_pow' hg0, hmg, mul_one]

/-- `P'` vanishes exactly at the roots of `g`. -/
theorem derivative_eval_eq_zero_iff {m r : ℕ} (hr : 3 ≤ r) (hrm : r < m) (β : K) :
    (derivative (polP K m r)).eval β = 0 ↔ (polG K (m - r)).eval β = 0 := by
  rw [derivative_polP_eq_pow hr hrm, eval_pow, pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)]

end Roots

section OverF2

/-- **Theorem 4.1(3).** `gcd(g, E) = 1` in `𝔽₂[X]`. -/
theorem isCoprime_polG_polE {m r : ℕ} (hr : 2 ≤ r) (hrm : r < m) (hrodd : Odd r)
    (hcop : Nat.Coprime r m) : IsCoprime (polG (ZMod 2) (m - r)) (polE (ZMod 2) m r) := by
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ZMod 2)
    (AlgebraicClosure (ZMod 2)) _ _).mpr ?_
  intro a
  rw [aeval_def, aeval_def, ← eval_map, ← eval_map, map_polG, map_polE]
  by_cases h : (polG (AlgebraicClosure (ZMod 2)) (m - r)).eval a = 0
  · exact Or.inr (evalE_ne_zero_at_root hr hrm hrodd hcop h)
  · exact Or.inl h

theorem natDegree_polG {s : ℕ} (hs : 1 ≤ s) : (polG (ZMod 2) s).natDegree = 2 ^ s := by
  unfold polG
  have h1 : (X + 1 : (ZMod 2)[X]).natDegree < 2 ^ s := by
    rw [← C_1, natDegree_X_add_C]; exact Nat.one_lt_two_pow (by omega)
  rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]

/-- **Theorem 4.1(2): `g` has exactly `2^s` roots in `\bar 𝔽₂`.** -/
theorem card_roots_polG {s : ℕ} (hs : 1 ≤ s) :
    Fintype.card ((polG (ZMod 2) s).rootSet (AlgebraicClosure (ZMod 2))) = 2 ^ s := by
  rw [card_rootSet_eq_natDegree (separable_polG hs) (IsAlgClosed.splits _), natDegree_polG hs]

end OverF2

end ResidueAPN
