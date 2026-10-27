import Apn2R03.FamilyBase

/-!
# The family P_{m,3}: residue-level facts (Claude, 2026-10-25)

F = X + X² + X³ + X^(1+u) + X^(2+u) + X^(2+v) + X^(u+v),  u = 2^(m-2), v = 2^(m-1).
Over K = F_q (q = 2^m, m ≥ 5 odd, gcd(3, m) = 1):
* p' = 1 + x² + x^u, ρ = 1 (I1); Λ ≡ 0 (I3); p^[2] = 1 + x + x^u + x^v, μ = 1 (I2);
* (H) holds, hence `Hyp`.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

noncomputable def Fnat3 (R : Type*) [CommRing R] (m : ℕ) : R[X] :=
  X + X ^ 2 + X ^ 3 + X ^ (1 + 2 ^ (m - 2)) + X ^ (2 + 2 ^ (m - 2)) + X ^ (2 + 2 ^ (m - 1))
    + X ^ (2 ^ (m - 2) + 2 ^ (m - 1))

noncomputable def J3 (R : Type*) [CommRing R] (m : ℕ) : R[X] := X ^ (2 + 2 ^ (m - 2))

noncomputable def Fsh3 (R : Type*) [CommRing R] (m : ℕ) : R[X] := Fnat3 R m + C 2 * (J3 R m) ^ 2

theorem Fnat3_map {R K : Type*} [CommRing R] [CommRing K] (π : R →+* K) (m : ℕ) :
    (Fnat3 R m).map π = Fnat3 K m := by
  simp [Fnat3, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]

section residue
variable {K : Type*} [Field K] [CharP K 2]

theorem deriv_X_pow_eval (n : ℕ) (x : K) : ((X : K[X]) ^ n).derivative.eval x = (n : K) * x ^ (n - 1) := by
  simp [derivative_X_pow]

theorem p3_eval (m : ℕ) (x : K) : (Fnat3 K m).eval x =
    x + x ^ 2 + x ^ 3 + x * x ^ (2 ^ (m - 2)) + x ^ 2 * x ^ (2 ^ (m - 2)) + x ^ 2 * x ^ (2 ^ (m - 1))
      + x ^ (2 ^ (m - 2)) * x ^ (2 ^ (m - 1)) := by
  simp only [Fnat3, eval_add, eval_pow, eval_X]
  ring

theorem p3_deriv (m : ℕ) (hm : 3 ≤ m) (x : K) :
    (Fnat3 K m).derivative.eval x = 1 + x ^ 2 + x ^ (2 ^ (m - 2)) := by
  have hu : ((2 ^ (m - 2) : ℕ) : K) = 0 := natCast_two_pow _ (by omega)
  have hv : ((2 ^ (m - 1) : ℕ) : K) = 0 := natCast_two_pow _ (by omega)
  have h2 : (2 : K) = 0 := two_K
  simp only [Fnat3, derivative_add, eval_add, deriv_X_pow_eval, derivative_X, eval_one]
  have e1 : 1 + 2 ^ (m - 2) - 1 = 2 ^ (m - 2) := by generalize 2 ^ (m - 2) = w; omega
  have e2 : 2 + 2 ^ (m - 2) - 1 = 1 + 2 ^ (m - 2) := by generalize 2 ^ (m - 2) = w; omega
  rw [e1, e2]
  push_cast at hu hv ⊢
  rw [hu, hv, h2]
  linear_combination x ^ 2 * h2

theorem p3_hasse2 (m : ℕ) (hm : 5 ≤ m) (x : K) :
    (hasseDeriv 2 (Fnat3 K m)).eval x = 1 + x + x ^ (2 ^ (m - 2)) + x ^ (2 ^ (m - 1)) := by
  have hX : ∀ n : ℕ, (hasseDeriv 2 ((X : K[X]) ^ n)).eval x = ((n.choose 2 : ℕ) : K) * x ^ (n - 2) := by
    intro n
    rw [X_pow_eq_monomial, hasseDeriv_monomial]
    simp [eval_monomial]
  simp only [Fnat3, map_add, eval_add, hX]
  have hX1 : (hasseDeriv 2 (X : K[X])).eval x = 0 := by
    have := hX 1; simpa using this
  rw [hX1]
  simp only [choose2_cast]
  have hu : 2 ^ (m - 2) = 2 * 2 ^ (m - 3) := by
    rw [show m - 2 = (m - 3) + 1 by omega, pow_succ]; ring
  have hv : 2 ^ (m - 1) = 4 * 2 ^ (m - 3) := by
    rw [show m - 1 = (m - 3) + 2 by omega, pow_add]; ring
  have d4 : (1 + 2 ^ (m - 2)) / 2 = 2 ^ (m - 3) := by rw [hu]; generalize 2 ^ (m - 3) = w; omega
  have d5 : (2 + 2 ^ (m - 2)) / 2 = 1 + 2 ^ (m - 3) := by rw [hu]; generalize 2 ^ (m - 3) = w; omega
  have d6 : (2 + 2 ^ (m - 1)) / 2 = 1 + 2 ^ (m - 2) := by rw [hu, hv]; generalize 2 ^ (m - 3) = w; omega
  have d7 : (2 ^ (m - 2) + 2 ^ (m - 1)) / 2 = 2 ^ (m - 3) + 2 ^ (m - 2) := by
    rw [hu, hv]; generalize 2 ^ (m - 3) = w; omega
  have e5 : 2 + 2 ^ (m - 2) - 2 = 2 ^ (m - 2) := by generalize 2 ^ (m - 2) = w; omega
  have e6 : 2 + 2 ^ (m - 1) - 2 = 2 ^ (m - 1) := by generalize 2 ^ (m - 1) = w; omega
  rw [d4, d5, d6, d7, e5, e6]
  have z3 : ((2 ^ (m - 3) : ℕ) : K) = 0 := natCast_two_pow _ (by omega)
  have z2 : ((2 ^ (m - 2) : ℕ) : K) = 0 := natCast_two_pow _ (by omega)
  push_cast at z3 z2 ⊢
  rw [z3, z2]
  norm_num
  try ring

/-- Λ ≡ 0 -/
theorem p3_Lam (m : ℕ) (hm : 3 ≤ m) (x : K) :
    (Fnat3 K m).eval (x + 1) - (Fnat3 K m).eval x - 1 * (Fnat3 K m).derivative.eval x = 0 := by
  rw [p3_eval, p3_eval, p3_deriv m hm]
  have hu : (x + 1) ^ (2 ^ (m - 2)) = x ^ (2 ^ (m - 2)) + 1 := by rw [frob_add, one_pow]
  have hv : (x + 1) ^ (2 ^ (m - 1)) = x ^ (2 ^ (m - 1)) + 1 := by rw [frob_add, one_pow]
  rw [hu, hv]
  have h2 : (2 : K) = 0 := two_K
  set U := x ^ (2 ^ (m - 2))
  set V := x ^ (2 ^ (m - 1))
  linear_combination (U * x + U + V * x + V + 2 * x ^ 2 + 5 * x + 3) * h2

theorem p3_deriv_add (m : ℕ) (hm : 3 ≤ m) (x y : K) :
    (Fnat3 K m).derivative.eval (x + y) =
      (Fnat3 K m).derivative.eval x + (Fnat3 K m).derivative.eval y - (Fnat3 K m).derivative.eval 0 := by
  rw [p3_deriv m hm, p3_deriv m hm, p3_deriv m hm, p3_deriv m hm, frob_add]
  have h1 := frob_add (K := K) 1 x y
  simp only [pow_one] at h1
  rw [h1, zero_pow (by norm_num), zero_pow (by positivity)]
  ring

/-- the kernel of the linear part of p' is {0, 1} -/
theorem p3_ker [Fintype K] (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m)
    (h3 : Nat.Coprime 3 m) (x : K) :
    (Fnat3 K m).derivative.eval x = (Fnat3 K m).derivative.eval 0 ↔ (x = 0 ∨ x = 1) := by
  rw [p3_deriv m (by omega), p3_deriv m (by omega)]
  have h2 : (2 : K) = 0 := two_K
  have hz : (0 : K) ^ (2 ^ (m - 2)) = 0 := zero_pow (by positivity)
  rw [hz]
  constructor
  · intro h
    have hxu : x ^ (2 ^ (m - 2)) = x ^ 2 := by
      have : x ^ 2 + x ^ (2 ^ (m - 2)) = 0 := by linear_combination h
      linear_combination this - x ^ 2 * h2
    have hq : x ^ (2 ^ m) = x := by rw [← hcard, FiniteField.pow_card]
    have h8 : x ^ (2 ^ 3) = x := by
      have e : x ^ (2 ^ m) = (x ^ (2 ^ (m - 2))) ^ (2 ^ 2) := by
        rw [← pow_mul, ← pow_add]; congr 2; omega
      rw [e, hxu, ← pow_mul] at hq
      simpa using hq
    have h1 := frob_gcd x 3 m h8 hq
    rw [h3, pow_one] at h1
    have : x * (x - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl)
    · simp [hz]
    · simp only [one_pow]; linear_combination h2

theorem quad_add {p q : K[X]} (hp : IsQuadSupport p) (hq : IsQuadSupport q) :
    IsQuadSupport (p + q) := by
  intro e he
  rcases mem_union.mp (support_add he) with h | h
  · exact hp e h
  · exact hq e h

theorem quad_Xpow {n : ℕ} (h : n = 0 ∨ (∃ i, n = 2 ^ i) ∨ (∃ i j, i < j ∧ n = 2 ^ i + 2 ^ j)) :
    IsQuadSupport ((X : K[X]) ^ n) := by
  intro e he
  rw [X_pow_eq_monomial] at he
  have := support_monomial' n (1 : K) he
  rw [mem_singleton.mp this]; exact h

theorem p3_quad (m : ℕ) (hm5 : 5 ≤ m) : IsQuadSupport (Fnat3 K m) := by
  unfold Fnat3
  refine quad_add (quad_add (quad_add (quad_add (quad_add (quad_add ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · rw [← pow_one (X : K[X])]; exact quad_Xpow (Or.inr (Or.inl ⟨0, by norm_num⟩))
  · exact quad_Xpow (Or.inr (Or.inl ⟨1, by norm_num⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨0, 1, by norm_num, by norm_num⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨0, m - 2, by omega, by norm_num⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨1, m - 2, by omega, by norm_num⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨1, m - 1, by omega, by norm_num⟩))
  · exact quad_Xpow (Or.inr (Or.inr ⟨m - 2, m - 1, by omega, rfl⟩))

theorem p3_apn [Fintype K] [DecidableEq K] (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m)
    (h3 : Nat.Coprime 3 m) (b : K) :
    (univ.filter (fun x : K => (Fnat3 K m).eval (x + 1) - (Fnat3 K m).eval x = b)).card ≤ 2 := by
  have hD : ∀ x : K, (Fnat3 K m).eval (x + 1) - (Fnat3 K m).eval x = (Fnat3 K m).derivative.eval x := by
    intro x; have := p3_Lam m (by omega) x; linear_combination this
  by_cases hne : (univ.filter (fun x : K => (Fnat3 K m).eval (x + 1) - (Fnat3 K m).eval x = b)).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    simp only [mem_filter, mem_univ, true_and, hD] at hx0
    have hsub : univ.filter (fun x : K => (Fnat3 K m).eval (x + 1) - (Fnat3 K m).eval x = b) ⊆ {x0, x0 + 1} := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and, hD] at hx
      have hadd := p3_deriv_add (K := K) m (by omega) x0 (x - x0)
      rw [show x0 + (x - x0) = x by ring, hx, hx0] at hadd
      have hk : (Fnat3 K m).derivative.eval (x - x0) = (Fnat3 K m).derivative.eval 0 := by
        linear_combination -hadd
      rcases (p3_ker m hm5 hcard h3 _).mp hk with h | h
      · simp [sub_eq_zero.mp h]
      · simp only [mem_insert, mem_singleton]; right; linear_combination h
    exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans (by simp))
  · rw [not_nonempty_iff_eq_empty.mp hne]; simp

end residue

end APN2
