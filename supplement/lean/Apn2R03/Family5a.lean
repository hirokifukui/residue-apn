import Apn2R03.Family3c

/-!
# The family P_{m,r}, r ≥ 5: residue-level facts (Claude, 2026-10-25)

w = 2^(r-2), u = 2^(m-2), v = 2^(m-1), T = Σ_{i=0}^{r-3} X^(2^i).
Paper form: p = T + X^w + X^w·T + X^(w+u) + X^(w+v) + X^u·T + X^(u+v).
Lean form `F5` (proved equal to the paper form, `F5_eq_paper`): the explicit monomials
X, X², X^w, X^(w+1), X^(w+2), X^(w+u), X^(w+v), X^(u+1), X^(u+2), X^(u+v) plus the tail
Z5 = Σ_{i<r-4} (X^(2^(i+2)) + X^(w+2^(i+2)) + X^(u+2^(i+2))), whose exponents are all ≡ 0 mod 4.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

noncomputable def Z5 (R : Type*) [CommRing R] (m r : ℕ) : R[X] :=
  ∑ i ∈ range (r - 4), (X ^ (2 ^ (i + 2)) + X ^ (2 ^ (r - 2) + 2 ^ (i + 2)) + X ^ (2 ^ (m - 2) + 2 ^ (i + 2)))

noncomputable def F5 (R : Type*) [CommRing R] (m r : ℕ) : R[X] :=
  X + X ^ 2 + X ^ (2 ^ (r - 2)) + X ^ (2 ^ (r - 2) + 1) + X ^ (2 ^ (r - 2) + 2)
    + X ^ (2 ^ (r - 2) + 2 ^ (m - 2)) + X ^ (2 ^ (r - 2) + 2 ^ (m - 1))
    + X ^ (2 ^ (m - 2) + 1) + X ^ (2 ^ (m - 2) + 2) + X ^ (2 ^ (m - 2) + 2 ^ (m - 1)) + Z5 R m r

noncomputable def Fsh5 (R : Type*) [CommRing R] (m r : ℕ) : R[X] := F5 R m r + C 2 * X ^ 3

noncomputable def T5 (R : Type*) [CommRing R] (r : ℕ) : R[X] := ∑ i ∈ range (r - 2), X ^ (2 ^ i)

noncomputable def P5paper (R : Type*) [CommRing R] (m r : ℕ) : R[X] :=
  T5 R r + X ^ (2 ^ (r - 2)) + X ^ (2 ^ (r - 2)) * T5 R r + X ^ (2 ^ (r - 2) + 2 ^ (m - 2))
    + X ^ (2 ^ (r - 2) + 2 ^ (m - 1)) + X ^ (2 ^ (m - 2)) * T5 R r + X ^ (2 ^ (m - 2) + 2 ^ (m - 1))

theorem T5_split (R : Type*) [CommRing R] (r : ℕ) (hr : 4 ≤ r) :
    T5 R r = X + X ^ 2 + ∑ i ∈ range (r - 4), X ^ (2 ^ (i + 2)) := by
  unfold T5
  rw [show r - 2 = (r - 4) + 1 + 1 by omega, sum_range_succ', sum_range_succ']
  simp only [pow_zero, pow_one, zero_add]
  ring

theorem F5_eq_paper (R : Type*) [CommRing R] (m r : ℕ) (hr : 4 ≤ r) :
    F5 R m r = P5paper R m r := by
  unfold F5 P5paper Z5
  rw [T5_split R r hr]
  simp only [sum_add_distrib, pow_add, mul_add, mul_sum]
  ring

theorem F5_map {R K : Type*} [CommRing R] [CommRing K] (π : R →+* K) (m r : ℕ) :
    (F5 R m r).map π = F5 K m r := by
  simp [F5, Z5, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]

section residue
variable {K : Type*} [Field K] [CharP K 2]

theorem cast_two_pow_add (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : ((2 ^ a + 2 ^ b : ℕ) : K) = 0 := by
  push_cast
  rw [two_K, zero_pow (by omega), zero_pow (by omega), add_zero]

theorem z5_deriv (m r : ℕ) (hm : 3 ≤ m) (hr : 3 ≤ r) (x : K) : (Z5 K m r).derivative.eval x = 0 := by
  unfold Z5
  rw [derivative_sum, eval_finsetSum]
  apply sum_eq_zero
  intro i _
  simp only [derivative_add, eval_add, deriv_X_pow_eval]
  rw [natCast_two_pow _ (by omega), cast_two_pow_add _ _ (by omega) (by omega),
    cast_two_pow_add _ _ (by omega) (by omega)]
  ring

theorem p5_deriv (m r : ℕ) (hm : 3 ≤ m) (hr : 3 ≤ r) (x : K) :
    (F5 K m r).derivative.eval x = 1 + x ^ (2 ^ (r - 2)) + x ^ (2 ^ (m - 2)) := by
  have h2 : (2 : K) = 0 := two_K
  unfold F5
  simp only [derivative_add, eval_add, deriv_X_pow_eval, derivative_X, eval_one]
  rw [z5_deriv m r hm hr]
  have e1 : 2 ^ (r - 2) + 1 - 1 = 2 ^ (r - 2) := by generalize 2 ^ (r - 2) = w; omega
  have e2 : 2 ^ (m - 2) + 1 - 1 = 2 ^ (m - 2) := by generalize 2 ^ (m - 2) = w; omega
  rw [e1, e2, natCast_two_pow _ (by omega), cast_two_pow_add _ _ (by omega) (by omega),
    cast_two_pow_add _ _ (by omega) (by omega), cast_two_pow_add _ _ (by omega) (by omega)]
  push_cast
  rw [two_K, zero_pow (show r - 2 ≠ 0 by omega), zero_pow (show m - 2 ≠ 0 by omega)]
  ring

theorem h2_eval (n : ℕ) (x : K) :
    (hasseDeriv 2 ((X : K[X]) ^ n)).eval x = ((n / 2 : ℕ) : K) * x ^ (n - 2) := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  simp only [eval_monomial, choose2_cast, mul_one]

theorem h2_4k (k : ℕ) (x : K) : (hasseDeriv 2 ((X : K[X]) ^ (4 * k))).eval x = 0 := by
  rw [h2_eval, show 4 * k / 2 = 2 * k by omega]; push_cast; rw [two_K]; ring

theorem h2_4k1 (k : ℕ) (x : K) : (hasseDeriv 2 ((X : K[X]) ^ (4 * k + 1))).eval x = 0 := by
  rw [h2_eval, show (4 * k + 1) / 2 = 2 * k by omega]; push_cast; rw [two_K]; ring

theorem h2_4k2 (k : ℕ) (x : K) :
    (hasseDeriv 2 ((X : K[X]) ^ (4 * k + 2))).eval x = x ^ (4 * k) := by
  rw [h2_eval, show (4 * k + 2) / 2 = 2 * k + 1 by omega, show 4 * k + 2 - 2 = 4 * k by omega]
  push_cast; rw [two_K]; ring

theorem p5_hasse2 (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) (x : K) :
    (hasseDeriv 2 (F5 K m r)).eval x = 1 + x ^ (2 ^ (r - 2)) + x ^ (2 ^ (m - 2)) := by
  have ew : 2 ^ (r - 2) = 4 * 2 ^ (r - 4) := by
    rw [show r - 2 = (r - 4) + 2 by omega, pow_add]; ring
  have eu : 2 ^ (m - 2) = 4 * 2 ^ (m - 4) := by
    rw [show m - 2 = (m - 4) + 2 by omega, pow_add]; ring
  have ev : 2 ^ (m - 1) = 4 * 2 ^ (m - 3) := by
    rw [show m - 1 = (m - 3) + 2 by omega, pow_add]; ring
  have hz : (hasseDeriv 2 (Z5 K m r)).eval x = 0 := by
    unfold Z5
    rw [map_sum, eval_finsetSum]
    apply sum_eq_zero
    intro i _
    have ei : 2 ^ (i + 2) = 4 * 2 ^ i := by rw [pow_add]; ring
    rw [map_add, map_add, eval_add, eval_add, ei, ew, eu, ← mul_add, ← mul_add, h2_4k, h2_4k, h2_4k]
    ring
  unfold F5
  simp only [map_add, eval_add]
  rw [hz]
  have hX1 : (hasseDeriv 2 (X : K[X])).eval x = 0 := by
    have := h2_eval (K := K) 1 x; simpa using this
  have hX2 : (hasseDeriv 2 ((X : K[X]) ^ 2)).eval x = 1 := by
    have := h2_4k2 (K := K) 0 x; simpa using this
  rw [hX1, hX2, ew, eu, ev, h2_4k, h2_4k1, h2_4k2, ← mul_add, h2_4k, ← mul_add, h2_4k, h2_4k1,
    h2_4k2, ← mul_add, h2_4k]
  ring

theorem odd_cast_one (n : ℕ) (hn : Odd n) : ((n : ℕ) : K) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  push_cast; rw [two_K]; ring

theorem z5_shift (m r : ℕ) (hr5 : 5 ≤ r) (hodd : Odd r) (x : K) :
    (∑ i ∈ range (r - 4), ((x + 1) ^ (2 ^ (i + 2)) + (x + 1) ^ (2 ^ (r - 2)) * (x + 1) ^ (2 ^ (i + 2))
          + (x + 1) ^ (2 ^ (m - 2)) * (x + 1) ^ (2 ^ (i + 2))))
      - ∑ i ∈ range (r - 4), (x ^ (2 ^ (i + 2)) + x ^ (2 ^ (r - 2)) * x ^ (2 ^ (i + 2))
          + x ^ (2 ^ (m - 2)) * x ^ (2 ^ (i + 2)))
      = 1 + x ^ (2 ^ (r - 2)) + x ^ (2 ^ (m - 2)) := by
  rw [← sum_sub_distrib]
  have hterm : ∀ i ∈ range (r - 4),
      ((x + 1) ^ (2 ^ (i + 2)) + (x + 1) ^ (2 ^ (r - 2)) * (x + 1) ^ (2 ^ (i + 2))
          + (x + 1) ^ (2 ^ (m - 2)) * (x + 1) ^ (2 ^ (i + 2)))
        - (x ^ (2 ^ (i + 2)) + x ^ (2 ^ (r - 2)) * x ^ (2 ^ (i + 2))
          + x ^ (2 ^ (m - 2)) * x ^ (2 ^ (i + 2)))
        = 1 + x ^ (2 ^ (r - 2)) + x ^ (2 ^ (m - 2)) := by
    intro i _
    rw [frob_add, frob_add, frob_add, one_pow, one_pow, one_pow]
    linear_combination (1 + x ^ (2 ^ (i + 2))) * (two_K : (2 : K) = 0)
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul,
    odd_cast_one _ (by obtain ⟨k, hk⟩ := hodd; exact ⟨k - 2, by omega⟩), one_mul]

/-- Λ ≡ 0 for r ≥ 5 -/
theorem p5_Lam (m r : ℕ) (hm : 3 ≤ m) (hr5 : 5 ≤ r) (hodd : Odd r) (x : K) :
    (F5 K m r).eval (x + 1) - (F5 K m r).eval x - 1 * (F5 K m r).derivative.eval x = 0 := by
  have hZ := z5_shift (K := K) m r hr5 hodd x
  rw [p5_deriv m r hm (by omega)]
  unfold F5 Z5
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_finsetSum, pow_add, pow_one] at hZ ⊢
  have hA : (x + 1) ^ (2 ^ (r - 2)) = x ^ (2 ^ (r - 2)) + 1 := by rw [frob_add, one_pow]
  have hB : (x + 1) ^ (2 ^ (m - 2)) = x ^ (2 ^ (m - 2)) + 1 := by rw [frob_add, one_pow]
  have hC : (x + 1) ^ (2 ^ (m - 1)) = x ^ (2 ^ (m - 1)) + 1 := by rw [frob_add, one_pow]
  rw [hA, hB] at hZ
  rw [hA, hB, hC]
  set A := x ^ (2 ^ (r - 2))
  set B := x ^ (2 ^ (m - 2))
  set C := x ^ (2 ^ (m - 1))
  linear_combination hZ + (A * x + 2 * A + B * x + 2 * B + C + x ^ 2 + 4 * x + 5) * (two_K : (2 : K) = 0)

theorem p5_deriv_add (m r : ℕ) (hm : 3 ≤ m) (hr : 3 ≤ r) (x y : K) :
    (F5 K m r).derivative.eval (x + y) =
      (F5 K m r).derivative.eval x + (F5 K m r).derivative.eval y - (F5 K m r).derivative.eval 0 := by
  rw [p5_deriv m r hm hr, p5_deriv m r hm hr, p5_deriv m r hm hr, p5_deriv m r hm hr, frob_add, frob_add,
    zero_pow (by positivity), zero_pow (by positivity)]
  ring

theorem p5_ker [Fintype K] (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (_hrm : r < m)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (x : K) :
    (F5 K m r).derivative.eval x = (F5 K m r).derivative.eval 0 ↔ (x = 0 ∨ x = 1) := by
  rw [p5_deriv m r (by omega) (by omega), p5_deriv m r (by omega) (by omega)]
  have h2 : (2 : K) = 0 := two_K
  rw [zero_pow (by positivity), zero_pow (by positivity)]
  constructor
  · intro h
    have hAB : x ^ (2 ^ (r - 2)) = x ^ (2 ^ (m - 2)) := by
      have : x ^ (2 ^ (r - 2)) + x ^ (2 ^ (m - 2)) = 0 := by linear_combination h
      linear_combination this - x ^ (2 ^ (m - 2)) * h2
    have hq : x ^ (2 ^ m) = x := by rw [← hcard, FiniteField.pow_card]
    have hr' : x ^ (2 ^ r) = x := by
      have e1 : x ^ (2 ^ r) = (x ^ (2 ^ (r - 2))) ^ (2 ^ 2) := by
        rw [← pow_mul, ← pow_add]; congr 2; omega
      have e2 : x ^ (2 ^ m) = (x ^ (2 ^ (m - 2))) ^ (2 ^ 2) := by
        rw [← pow_mul, ← pow_add]; congr 2; omega
      rw [e1, hAB, ← e2, hq]
    have h1 := frob_gcd x r m hr' hq
    rw [hcop, pow_one] at h1
    have : x * (x - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl)
    · simp [zero_pow (show 2 ^ (r - 2) ≠ 0 by positivity), zero_pow (show 2 ^ (m - 2) ≠ 0 by positivity)]
    · simp only [one_pow]; linear_combination h2

theorem quad_zero : IsQuadSupport (0 : K[X]) := by intro e he; simp at he

theorem quad_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → K[X]) :
    (∀ i ∈ s, IsQuadSupport (f i)) → IsQuadSupport (∑ i ∈ s, f i) := by
  refine Finset.induction_on s (fun _ => by rw [sum_empty]; exact quad_zero) ?_
  intro a s ha ih h
  rw [sum_insert ha]
  exact quad_add (h a (mem_insert_self _ _)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem p5_quad (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) : IsQuadSupport (F5 K m r) := by
  have hZ : IsQuadSupport (Z5 K m r) := by
    unfold Z5
    apply quad_sum
    intro i hi
    have hi' := mem_range.mp hi
    exact quad_add (K := K) (quad_add (quad_Xpow (Or.inr (Or.inl ⟨i + 2, rfl⟩)))
      (quad_Xpow (Or.inr (Or.inr ⟨i + 2, r - 2, by omega, by ring⟩))))
      (quad_Xpow (Or.inr (Or.inr ⟨i + 2, m - 2, by omega, by ring⟩)))
  unfold F5
  refine quad_add (quad_add (quad_add (quad_add (quad_add (quad_add (quad_add (quad_add (quad_add
    (quad_add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) hZ
  · rw [← pow_one (X : K[X])]; exact quad_Xpow (Or.inr (Or.inl ⟨0, by norm_num⟩))
  · exact quad_Xpow (Or.inr (Or.inl ⟨1, by norm_num⟩))
  · exact quad_Xpow (Or.inr (Or.inl ⟨r - 2, rfl⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨0, r - 2, by omega, by ring⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨1, r - 2, by omega, by ring⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨r - 2, m - 2, by omega, rfl⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨r - 2, m - 1, by omega, rfl⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨0, m - 2, by omega, by ring⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨1, m - 2, by omega, by ring⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨m - 2, m - 1, by omega, rfl⟩))

theorem p5_apn [Fintype K] [DecidableEq K] (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m)
    (hodd : Odd r) (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (b : K) :
    (univ.filter (fun x : K => (F5 K m r).eval (x + 1) - (F5 K m r).eval x = b)).card ≤ 2 := by
  have hD : ∀ x : K, (F5 K m r).eval (x + 1) - (F5 K m r).eval x = (F5 K m r).derivative.eval x := by
    intro x; have := p5_Lam m r (by omega) hr5 hodd x; linear_combination this
  by_cases hne : (univ.filter (fun x : K => (F5 K m r).eval (x + 1) - (F5 K m r).eval x = b)).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    simp only [mem_filter, mem_univ, true_and, hD] at hx0
    have hsub : univ.filter (fun x : K => (F5 K m r).eval (x + 1) - (F5 K m r).eval x = b) ⊆
        {x0, x0 + 1} := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and, hD] at hx
      have hadd := p5_deriv_add (K := K) m r (by omega) (by omega) x0 (x - x0)
      rw [show x0 + (x - x0) = x by ring, hx, hx0] at hadd
      have hk : (F5 K m r).derivative.eval (x - x0) = (F5 K m r).derivative.eval 0 := by
        linear_combination -hadd
      rcases (p5_ker m r hm5 hr5 hrm hcard hcop _).mp hk with h | h
      · simp [sub_eq_zero.mp h]
      · simp only [mem_insert, mem_singleton]; right; linear_combination h
    exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans (by simp))
  · rw [not_nonempty_iff_eq_empty.mp hne]; simp

end residue

end APN2
