import Apn2R03.Inter

/-!
# Intermediate layers, part 2: the polynomial `T` and its local data (Claude, 2026-10-26, R05c)
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

/-! ## The polynomial `T` with `α T(x) = F(x+α) − F(x)` -/

theorem hasse_map {R' : Type*} [CommRing R'] (φ : R →+* R') (i : ℕ) (f : R[X]) :
    (hasseDeriv i f).map φ = hasseDeriv i (f.map φ) := by
  ext n
  simp only [coeff_map, hasseDeriv_coeff, map_mul, map_natCast]

theorem pi_hasse (i : ℕ) (f : R[X]) (x : R) :
    S.π ((hasseDeriv i f).eval x) = (hasseDeriv i (f.map S.π)).eval (S.π x) := by
  rw [S.pi_eval, hasse_map]

theorem hasse_hasse (a b : ℕ) (f : R[X]) :
    hasseDeriv a (hasseDeriv b f) = (a + b).choose a • hasseDeriv (a + b) f := by
  have := congrArg (fun L => L f) (hasseDeriv_comp (R := R) a b)
  simpa using this

/-- `T = Σ α^i F^[i+1]` -/
noncomputable def Tpol (f : R[X]) (α : R) : R[X] :=
  ∑ i ∈ range (f.natDegree + 3), C (α ^ i) * hasseDeriv (i + 1) f

theorem Tpol_eval_mul (f : R[X]) (α x : R) :
    α * (Tpol f α).eval x = f.eval (x + α) - f.eval x := by
  have h := eval_eq_sum_range' (p := taylor x f) (n := f.natDegree + 4)
    (by rw [natDegree_taylor]; omega) α
  rw [taylor_eval, Finset.sum_range_succ'] at h
  simp only [taylor_coeff, hasseDeriv_zero, LinearMap.id_apply, pow_zero, mul_one] at h
  rw [add_comm x α, h]
  unfold Tpol
  simp only [eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasse_Tpol_eval (n : ℕ) (f : R[X]) (α x : R) :
    (hasseDeriv n (Tpol f α)).eval x =
      ∑ i ∈ range (f.natDegree + 3), α ^ i * (((i + 1 + n).choose n : ℕ) : R) *
        (hasseDeriv (i + 1 + n) f).eval x := by
  unfold Tpol
  simp only [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_eq_C_mul, map_smul, hasse_hasse, add_comm n (i + 1), eval_smul, smul_eq_mul, eval_smul,
    nsmul_eq_mul]
  ring

/-- split off the first two terms of a sum over `range (N + 3)` -/
theorem sum_split2 (N : ℕ) (g : ℕ → R) :
    ∑ i ∈ range (N + 3), g i = g 0 + g 1 + ∑ i ∈ range (N + 1), g (i + 2) := by
  rw [show N + 3 = N + 1 + 1 + 1 by ring, Finset.sum_range_succ', Finset.sum_range_succ']
  ring

/-- split off the first term -/
theorem sum_split1 (N : ℕ) (g : ℕ → R) :
    ∑ i ∈ range (N + 3), g i = g 0 + ∑ i ∈ range (N + 2), g (i + 1) := by
  rw [show N + 3 = N + 2 + 1 by ring, Finset.sum_range_succ']
  ring

theorem pi_three : S.π (3 : R) = 1 := by
  have h2 := S.two_F
  rw [show (3 : R) = 2 + 1 by norm_num, map_add, map_ofNat, map_one, h2, zero_add]

/-- `T(x) = F'(x) + α F^[2](x) + α² (…)` -/
theorem Tpol_split (f : R[X]) (α x : R) : ∃ s : R,
    (Tpol f α).eval x = f.derivative.eval x + α * (hasseDeriv 2 f).eval x + α ^ 2 * s := by
  refine ⟨∑ i ∈ range (f.natDegree + 1), α ^ i * (hasseDeriv (i + 3) f).eval x, ?_⟩
  unfold Tpol
  simp only [eval_finsetSum, eval_mul, eval_C]
  rw [sum_split2]
  simp only [pow_zero, one_mul, pow_one, zero_add, hasseDeriv_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring_nf

/-- `T'(x) = 2 g` with `π g = F̄^[2] + π(2^(j−1)) ū F̄^[3]` -/
theorem Tpol_deriv_spec (f : R[X]) (j : ℕ) (hj : 1 ≤ j) (u x : R) : ∃ g : R,
    (Tpol f (2 ^ j * u)).derivative.eval x = 2 * g ∧
      S.π g = S.π ((hasseDeriv 2 f).eval x) +
        S.π (2 ^ (j - 1)) * S.π u * S.π ((hasseDeriv 3 f).eval x) := by
  set α : R := 2 ^ j * u with hα
  refine ⟨(hasseDeriv 2 f).eval x + 2 ^ (j - 1) * u * 3 * (hasseDeriv 3 f).eval x +
      ∑ i ∈ range (f.natDegree + 1), 2 ^ (2 * j - 1) * u ^ 2 * (α ^ i *
        (((i + 2 + 1 + 1).choose 1 : ℕ) : R) * (hasseDeriv (i + 2 + 1 + 1) f).eval x), ?_, ?_⟩
  · rw [← hasseDeriv_one, hasse_Tpol_eval, sum_split2]
    have e1 : (2 : R) ^ j = 2 * 2 ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
    have e2 : (2 : R) ^ (2 * j) = 2 * 2 ^ (2 * j - 1) := by rw [← pow_succ']; congr 1; omega
    have hα2 : α ^ 2 = 2 ^ (2 * j) * u ^ 2 := by rw [hα, mul_pow, ← pow_mul, mul_comm j 2]
    simp only [pow_zero, one_mul, pow_one]
    have this : ∀ i ∈ range (f.natDegree + 1),
        α ^ (i + 2) * (((i + 2 + 1 + 1).choose 1 : ℕ) : R) * (hasseDeriv (i + 2 + 1 + 1) f).eval x =
        2 * (2 ^ (2 * j - 1) * u ^ 2 * (α ^ i * (((i + 2 + 1 + 1).choose 1 : ℕ) : R) *
          (hasseDeriv (i + 2 + 1 + 1) f).eval x)) := by
      intro i _
      rw [pow_add, hα2, e2]; ring
    have h0 : (((0 + 1 + 1).choose 1 : ℕ) : R) * eval x ((hasseDeriv (0 + 1 + 1)) f) =
        2 * eval x ((hasseDeriv 2) f) := by norm_num
    have h1 : α * (((1 + 1 + 1).choose 1 : ℕ) : R) * eval x ((hasseDeriv (1 + 1 + 1)) f) =
        2 * (2 ^ (j - 1) * u * 3 * eval x ((hasseDeriv 3) f)) := by
      rw [hα, e1]; norm_num; ring
    rw [h0, h1, Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  · have hpow : S.π ((2 : R) ^ (2 * j - 1)) = 0 := by
      rw [← mul_one ((2 : R) ^ (2 * j - 1)), S.pi_two_pow_mul _ (by omega)]
    have hz : ∀ i ∈ range (f.natDegree + 1), S.π (2 ^ (2 * j - 1) * u ^ 2 * (α ^ i *
        (((i + 2 + 1 + 1).choose 1 : ℕ) : R) * (hasseDeriv (i + 2 + 1 + 1) f).eval x)) = 0 := by
      intro i _
      rw [map_mul, map_mul, hpow, zero_mul, zero_mul]
    rw [map_add, map_sum, Finset.sum_eq_zero hz, add_zero, map_add, map_mul, map_mul, map_mul,
      S.pi_three, mul_one]

/-- `T^[2](x)` has residue `F̄^[3]` -/
theorem Tpol_hasse2_spec (f : R[X]) (α x : R) (hα : S.π α = 0) :
    S.π ((hasseDeriv 2 (Tpol f α)).eval x) = S.π ((hasseDeriv 3 f).eval x) := by
  rw [hasse_Tpol_eval, sum_split1, map_add, map_sum]
  have hz : ∀ i ∈ range (f.natDegree + 2), S.π (α ^ (i + 1) * (((i + 1 + 1 + 2).choose 2 : ℕ) : R) *
      (hasseDeriv (i + 1 + 1 + 2) f).eval x) = 0 := by
    intro i _
    rw [map_mul, map_mul, map_pow, hα, zero_pow (by omega), zero_mul, zero_mul]
  rw [Finset.sum_eq_zero hz, add_zero]
  simp only [pow_zero, one_mul, zero_add]
  rw [map_mul]
  norm_num
  rw [S.pi_three, one_mul]

/-- `π T(x) = F̄'(π x)` when `π α = 0` -/
theorem Tpol_pi (f : R[X]) (α x : R) (hα : S.π α = 0) :
    S.π ((Tpol f α).eval x) = (f.map S.π).derivative.eval (S.π x) := by
  obtain ⟨s, hs⟩ := Tpol_split f α x
  rw [hs, map_add, map_add, map_mul, map_mul, map_pow, hα, S.pi_deriv_eval]
  ring

/-- unit cancellation: `2^j u w = 0`, `π u ≠ 0` ⇒ `w ∈ 2^(k−j) R` -/
theorem unit_ann (j : ℕ) (hj : j ≤ S.k) (u w : R) (hu : S.π u ≠ 0) (h : 2 ^ j * u * w = 0) :
    ∃ v, w = 2 ^ (S.k - j) * v := by
  obtain ⟨v, hv⟩ := S.surj (S.π u)⁻¹
  have h1 : S.π (u * v - 1) = 0 := by rw [map_sub, map_mul, hv, map_one, mul_inv_cancel₀ hu, sub_self]
  obtain ⟨s, hs⟩ := (S.ker2 _).mp h1
  set x : R := 2 ^ j * w with hx
  have hx0 : x = 2 * (-s) * x := by
    have : x * (u * v) = 0 := by rw [hx]; linear_combination v * h
    linear_combination this - x * hs
  have hiter : ∀ n, x = (2 * (-s)) ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, ← hx0]; exact ih
  have : x = 0 := by
    rw [hiter S.k, mul_pow, S.nil, zero_mul, zero_mul]
  exact S.ann_two_pow j (S.k - j) (by omega) w this

end GRS

end APN2

#print axioms APN2.GRS.Tpol_eval_mul
#print axioms APN2.GRS.Tpol_deriv_spec
#print axioms APN2.GRS.Tpol_hasse2_spec
#print axioms APN2.GRS.unit_ann
