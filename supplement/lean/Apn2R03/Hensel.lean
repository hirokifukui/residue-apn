import Apn2R03.Basic

/-!
# Taylor expansion and the simple-root counting lemma (Claude, 2026-10-25)

* `taylor2`, `taylor3` : f(x+h) = f(x) + h f'(x) + h² Q,  f(x+h) = f(x) + h f'(x) + h² f^[2](x) + h³ Q.
* `card_T` : if all roots of P̄ = P mod 2 are simple, then for 1 ≤ j ≤ k
  #{z ∈ R : P(z) ∈ 2^j R} = N̄ · q^(k-j), where N̄ = #{roots of P̄ in F}.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

theorem taylor2 {R : Type*} [CommRing R] (f : R[X]) (x h : R) :
    ∃ Q : R, f.eval (x + h) = f.eval x + h * f.derivative.eval x + h ^ 2 * Q := by
  set g := taylor x f - C (f.eval x) - C (f.derivative.eval x) * X with hg
  have hdvd : (X : R[X]) ^ 2 ∣ g := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp [g, taylor_coeff_zero]
    · simp [g, taylor_coeff_one]
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q.eval h, ?_⟩
  have := congrArg (eval h) hq
  simp only [g, eval_sub, eval_C, eval_mul, eval_X, taylor_eval, eval_pow] at this
  rw [add_comm x h]
  linear_combination this

theorem taylor3 {R : Type*} [CommRing R] (f : R[X]) (x h : R) :
    ∃ Q : R, f.eval (x + h) = f.eval x + h * f.derivative.eval x
      + h ^ 2 * (hasseDeriv 2 f).eval x + h ^ 3 * Q := by
  set g := taylor x f - C (f.eval x) - C (f.derivative.eval x) * X
    - C ((hasseDeriv 2 f).eval x) * X ^ 2 with hg
  have hdvd : (X : R[X]) ^ 3 ∣ g := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp [g, taylor_coeff_zero]
    · simp [g, taylor_coeff_one]
    · simp [g, taylor_coeff, coeff_X_pow]
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q.eval h, ?_⟩
  have := congrArg (eval h) hq
  simp only [g, eval_sub, eval_C, eval_mul, eval_X, taylor_eval, eval_pow] at this
  rw [add_comm x h]
  linear_combination this

namespace GRS

variable {R F : Type*} [CommRing R] [Field F] (S : GRS R F)

theorem pi_eval (P : R[X]) (z : R) : S.π (P.eval z) = (P.map S.π).eval (S.π z) := by
  rw [eval_map, eval₂_at_apply]

theorem pi_deriv_eval (P : R[X]) (z : R) :
    S.π (P.derivative.eval z) = (P.map S.π).derivative.eval (S.π z) := by
  rw [S.pi_eval, derivative_map]

/-- first-order expansion modulo 2^(j+1) along 2^j w -/
theorem eval_add_two_pow (P : R[X]) (j : ℕ) (hj : 1 ≤ j) (z w : R) :
    ∃ c : R, P.eval (z + 2 ^ j * w) = P.eval z + 2 ^ j * (w * P.derivative.eval z)
      + 2 ^ (j + 1) * c := by
  obtain ⟨Q, hQ⟩ := taylor2 P z (2 ^ j * w)
  refine ⟨2 ^ (j - 1) * w ^ 2 * Q, ?_⟩
  rw [hQ]
  have : (2 : R) ^ (j + 1) * (2 ^ (j - 1) * w ^ 2 * Q) = (2 ^ j * w) ^ 2 * Q := by
    rw [mul_pow, ← pow_mul]
    have : j * 2 = (j + 1) + (j - 1) := by omega
    rw [this, pow_add]; ring
  rw [this]; ring

section card
variable [Fintype R] [DecidableEq R] [Fintype F] [DecidableEq F]

/-- the set `T_j = {z : P z ∈ 2^j R}` -/
def T (P : R[X]) (j : ℕ) : Finset R := univ.filter (fun z : R => ∃ w, P.eval z = 2 ^ j * w)

theorem mem_T (P : R[X]) (j : ℕ) (z : R) : z ∈ T P j ↔ ∃ w, P.eval z = 2 ^ j * w := by
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]

theorem root_of_mem_T (P : R[X]) (j : ℕ) (hj : 1 ≤ j) (z : R) (hz : z ∈ T P j) :
    (P.map S.π).eval (S.π z) = 0 := by
  obtain ⟨w, hw⟩ := (mem_T P j z).mp hz
  rw [← S.pi_eval, hw]
  exact S.pi_two_pow_mul j hj w

theorem card_T_one (hcard : Fintype.card R = Fintype.card F ^ S.k) (P : R[X]) :
    (T P 1).card =
      (univ.filter (fun t : F => (P.map S.π).eval t = 0)).card * Fintype.card F ^ (S.k - 1) := by
  have key := Finset.card_eq_sum_card_fiberwise (s := T P 1)
    (t := univ.filter (fun t : F => (P.map S.π).eval t = 0)) (f := fun z => S.π z)
    (fun z hz => Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.root_of_mem_T P 1 le_rfl z hz⟩))
  rw [key, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
  rw [← S.card_fiber hcard t]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_T]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    have : S.π (P.eval z) = 0 := by rw [S.pi_eval, h, ht]
    obtain ⟨y, hy⟩ := (S.ker2 _).mp this
    exact ⟨y, by rw [pow_one]; exact hy⟩

theorem card_T_succ (P : R[X])
    (hsimple : ∀ t : F, (P.map S.π).eval t = 0 → (P.map S.π).derivative.eval t ≠ 0)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j < S.k) :
    (T P j).card = (T P (j + 1)).card * Fintype.card F := by
  classical
  set L : F → R := Function.surjInv S.surj with hL
  have hLπ : ∀ s, S.π (L s) = s := Function.surjInv_eq S.surj
  rw [← Finset.card_univ (α := F), ← Finset.card_product]
  symm
  apply Finset.card_bij (fun (p : R × F) _ => p.1 + 2 ^ j * L p.2)
  · -- maps into T_j
    rintro ⟨z, s⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp
    obtain ⟨w, hw⟩ := (mem_T P _ z).mp hp
    obtain ⟨c, hc⟩ := eval_add_two_pow P j hj z (L s)
    rw [mem_T]
    refine ⟨2 * w + L s * P.derivative.eval z + 2 * c, ?_⟩
    simp only
    rw [hc, hw]; ring
  · -- injective
    rintro ⟨z, s⟩ hp ⟨z', s'⟩ hp' heq
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp hp' heq
    have hz' : z' = z + 2 ^ j * (L s - L s') := by linear_combination -heq
    obtain ⟨w, hw⟩ := (mem_T P _ z).mp hp
    obtain ⟨w', hw'⟩ := (mem_T P _ z').mp hp'
    obtain ⟨c, hc⟩ := eval_add_two_pow P j hj z (L s - L s')
    rw [← hz', hw', hw] at hc
    have hmem : ∃ v, 2 ^ j * ((L s - L s') * P.derivative.eval z) = 2 ^ (j + 1) * v :=
      ⟨w' - w - c, by linear_combination -hc⟩
    have h0 := (S.two_pow_mul_mem_iff j hjk _).mp hmem
    rw [map_mul, map_sub, hLπ, hLπ, S.pi_deriv_eval] at h0
    have hroot := S.root_of_mem_T P (j + 1) (by omega) z hp
    have hd := hsimple _ hroot
    have hss : s = s' := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hd
    subst hss
    have : z = z' := by rw [hz', sub_self, mul_zero, add_zero]
    rw [this]
  · -- surjective
    intro z' hz'
    obtain ⟨v, hv⟩ := (mem_T P j z').mp hz'
    have hroot := S.root_of_mem_T P j hj z' hz'
    have hd := hsimple _ hroot
    set s : F := S.π v / (P.map S.π).derivative.eval (S.π z') with hs
    refine ⟨(z' - 2 ^ j * L s, s), ?_, by simp⟩
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    rw [mem_T]
    obtain ⟨c, hc⟩ := eval_add_two_pow P j hj z' (-L s)
    have e1 : z' + 2 ^ j * -L s = z' - 2 ^ j * L s := by ring
    rw [e1, hv] at hc
    have hπ : S.π (v + -L s * P.derivative.eval z') = 0 := by
      rw [map_add, map_mul, map_neg, hLπ, S.pi_deriv_eval, hs]
      field_simp
      ring
    obtain ⟨y, hy⟩ := (S.ker2 _).mp hπ
    refine ⟨y + c, ?_⟩
    rw [hc]
    have : (2 : R) ^ j * v + 2 ^ j * (-L s * P.derivative.eval z') =
        2 ^ j * (v + -L s * P.derivative.eval z') := by ring
    rw [this, hy]; ring

theorem card_T (hcard : Fintype.card R = Fintype.card F ^ S.k) (P : R[X])
    (hsimple : ∀ t : F, (P.map S.π).eval t = 0 → (P.map S.π).derivative.eval t ≠ 0) :
    ∀ j, 1 ≤ j → j ≤ S.k →
      (T P j).card =
        (univ.filter (fun t : F => (P.map S.π).eval t = 0)).card * Fintype.card F ^ (S.k - j) := by
  intro j hj hjk
  induction j, hj using Nat.le_induction with
  | base => exact S.card_T_one hcard P
  | succ j hj ih =>
    have h1 := S.card_T_succ P hsimple j hj (by omega)
    rw [ih (by omega)] at h1
    have hq : 0 < Fintype.card F := Fintype.card_pos
    have : Fintype.card F ^ (S.k - j) = Fintype.card F ^ (S.k - (j + 1)) * Fintype.card F := by
      rw [← pow_succ]; congr 1; omega
    rw [this, ← mul_assoc] at h1
    exact (Nat.eq_of_mul_eq_mul_right hq h1).symm

end card

end GRS

end APN2

#print axioms APN2.taylor3
#print axioms APN2.GRS.card_T
