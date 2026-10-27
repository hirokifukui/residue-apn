import Apn2R03.Layers
import Apn2R03.Cards

/-!
# Intermediate layers: Theorem inter (Claude, 2026-10-26, R05c)

`α = 2^j u` with `π u ≠ 0`, `1 ≤ j`.
* `shift_inv`  : for `j + 2 ≤ k`, `F(x+α) − F(x)` is invariant under `x ↦ x + 2^(k−j−1) t`;
* `inter_dvd`  : (i) every entry of the row of `α` is a multiple of `q^(j+1)`.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

theorem two_pow_eq_zero (a : ℕ) (ha : S.k ≤ a) : (2 : R) ^ a = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a = S.k + d := ⟨a - S.k, by omega⟩
  rw [pow_add, S.nil, zero_mul]

theorem two_pow_mul_eq_zero (a : ℕ) (ha : S.k ≤ a) (y : R) : (2 : R) ^ a * y = 0 := by
  rw [S.two_pow_eq_zero a ha, zero_mul]

/-- Taylor expansion with all Hasse derivatives -/
theorem eval_add_hasse (g : R[X]) (x h : R) :
    g.eval (x + h) = ∑ i ∈ range (g.natDegree + 1), (hasseDeriv i g).eval x * h ^ i := by
  rw [add_comm, ← taylor_eval, eval_eq_sum_range, natDegree_taylor]
  simp only [taylor_coeff]

theorem deriv_deriv_eval (f : R[X]) (x : R) :
    f.derivative.derivative.eval x = 2 * (hasseDeriv 2 f).eval x := by
  have h : (Nat.factorial 2) • hasseDeriv 2 f = derivative (derivative f) := by
    have := congrFun (factorial_smul_hasseDeriv (R := R) (k := 2)) f
    simpa using this
  rw [← h, eval_smul, nsmul_eq_mul]
  norm_num [Nat.factorial]

/-- **Shift invariance** of `x ↦ F(x+α) − F(x)` along `2^(k−j−1) R`. -/
theorem shift_inv (f : R[X]) (j : ℕ) (hj : 1 ≤ j) (hjk : j + 2 ≤ S.k) (u x t : R) :
    f.eval (x + 2 ^ (S.k - j - 1) * t + 2 ^ j * u) - f.eval (x + 2 ^ (S.k - j - 1) * t) =
      f.eval (x + 2 ^ j * u) - f.eval x := by
  set α : R := 2 ^ j * u with hα
  set g : R[X] := f.comp (X + C α) - f with hgdef
  have hg : ∀ y, g.eval y = f.eval (y + α) - f.eval y := by
    intro y; simp [g, eval_comp]
  set h : R := 2 ^ (S.k - j - 1) * t with hh
  rw [← hg, ← hg, eval_add_hasse g x h, Finset.sum_range_succ']
  have hz : ∀ i, (hasseDeriv (i + 1) g).eval x * h ^ (i + 1) = 0 := by
    intro i
    have hd : (hasseDeriv (i + 1) g).eval x =
        (hasseDeriv (i + 1) f).eval (x + α) - (hasseDeriv (i + 1) f).eval x := by
      simp only [g, map_sub, eval_sub, hasse_comp_eval]
    rw [hd]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · -- first derivative
      rw [hasseDeriv_one]
      obtain ⟨Q, hQ⟩ := taylor2 f.derivative x α
      rw [hQ, deriv_deriv_eval f x]
      have e1 : (2 : R) ^ j * 2 * 2 ^ (S.k - j - 1) = 2 ^ S.k := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      have e2 : (2 : R) ^ j * 2 ^ j * 2 ^ (S.k - j - 1) = 2 ^ S.k * 2 ^ (j - 1) := by
        rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
      have : (f.derivative.eval x + α * (2 * (hasseDeriv 2 f).eval x) + α ^ 2 * Q -
          f.derivative.eval x) * h ^ (0 + 1) =
          ((2 : R) ^ j * 2 * 2 ^ (S.k - j - 1)) * (u * (hasseDeriv 2 f).eval x * t) +
          ((2 : R) ^ j * 2 ^ j * 2 ^ (S.k - j - 1)) * (u ^ 2 * Q * t) := by
        rw [hα, hh]; ring
      rw [this, e1, e2, S.nil]; ring
    · -- higher derivatives: the difference is divisible by α
      obtain ⟨c, hc⟩ := sub_dvd_eval_sub (x + α) x (hasseDeriv (i + 1) f)
      rw [hc, add_sub_cancel_left]
      have hle : (S.k - j - 1) * 2 ≤ (S.k - j - 1) * (i + 1) := Nat.mul_le_mul_left _ (by omega)
      have : α * c * h ^ (i + 1) = 2 ^ (j + (S.k - j - 1) * (i + 1)) * (u * c * t ^ (i + 1)) := by
        rw [hα, hh, mul_pow, ← pow_mul, pow_add]; ring
      rw [this]
      exact S.two_pow_mul_eq_zero _ (by omega) _
  simp only [hz, Finset.sum_const_zero, zero_add, hasseDeriv_zero, LinearMap.id_apply, pow_zero, mul_one]

section card
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- a set invariant under translation by `2^e R` has a multiple of `q^(k−e)` elements -/
theorem card_dvd_of_inv (hcard : Fintype.card R = Fintype.card K ^ S.k) (e : ℕ) (he : e ≤ S.k)
    (P : R → Prop) [DecidablePred P] (hinv : ∀ x t, P x → P (x + 2 ^ e * t)) :
    Fintype.card K ^ (S.k - e) ∣ (univ.filter P).card := by
  classical
  let φ : R → R ⧸ Ideal.span {(2 : R) ^ e} := Ideal.Quotient.mk _
  have key := Finset.card_eq_sum_card_fiberwise (s := univ.filter P) (t := (univ.filter P).image φ)
    (f := φ) (fun x hx => Finset.mem_coe.mpr (Finset.mem_image_of_mem φ (Finset.mem_coe.mp hx)))
  rw [key]
  apply Finset.dvd_sum
  intro c hc
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hc
  have hP0 : P x0 := (Finset.mem_filter.mp hx0).2
  have hfib : ((univ.filter P).filter (fun x => φ x = φ x0)) =
      (I (R := R) e).image (fun y => x0 + y) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, mem_I]
    constructor
    · rintro ⟨-, hx⟩
      have h1 : x - x0 ∈ Ideal.span {(2 : R) ^ e} := Ideal.Quotient.eq.mp hx
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
      exact ⟨2 ^ e * a, ⟨a, rfl⟩, by linear_combination ha⟩
    · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
      refine ⟨hinv x0 a hP0, ?_⟩
      apply Ideal.Quotient.eq.mpr
      exact Ideal.mem_span_singleton'.mpr ⟨a, by ring⟩
  rw [hfib, S.card_coset hcard e he]

/-- **Theorem inter (i)**: every entry of the row of `α = 2^j u` is a multiple of `q^(j+1)` (`1 ≤ j ≤ k−2`). -/
theorem inter_dvd (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (j : ℕ) (hj : 1 ≤ j)
    (hjk : j + 2 ≤ S.k) (u β : R) :
    Fintype.card K ^ (j + 1) ∣ delta f (2 ^ j * u) β := by
  unfold delta
  have h := S.card_dvd_of_inv hcard (S.k - j - 1) (by omega)
    (fun x => f.eval (x + 2 ^ j * u) - f.eval x = β)
    (fun x t hx => by rw [S.shift_inv f j hj hjk u x t]; exact hx)
  rwa [show S.k - (S.k - j - 1) = j + 1 by omega] at h

end card

end GRS

end APN2

#print axioms APN2.GRS.shift_inv
#print axioms APN2.GRS.inter_dvd
