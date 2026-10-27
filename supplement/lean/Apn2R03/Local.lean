import Apn2R03.Hensel

/-!
# The local count on one residue class (Claude, 2026-10-25)

For G ∈ R[X] and a lift x_a with G'(x_a) = 2g (π g ≠ 0):
* if G(x_a) = 4c then #{x : π x = π x_a, G x = 0} = q · #{y ∈ F : c̄ + ḡ y + h̄ y² = 0},
  h = G^[2](x_a)  (`class_count`);
* if G(x_a) ∉ 4R then the count is 0 (`class_count_zero`).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R F : Type*} [CommRing R] [Field F] (S : GRS R F)

theorem two_F (S : GRS R F) : (2 : F) = 0 := by
  have := S.pi_two; rwa [map_ofNat] at this

/-- the polynomial `P` with `4 P(z) = G(x_a + 2 z)` -/
theorem exists_local_poly (G : R[X]) (xa c g : R) (hc : G.eval xa = 4 * c)
    (hg : G.derivative.eval xa = 2 * g) :
    ∃ P : R[X], (∀ z, 4 * P.eval z = G.eval (xa + 2 * z)) ∧
      ∀ y : F, (P.map S.π).eval y = S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2
        ∧ (P.map S.π).derivative.eval y = S.π g := by
  set Tt := taylor xa G with hTt
  have hdvd : (X : R[X]) ^ 2 ∣ Tt - C (G.eval xa) - C (G.derivative.eval xa) * X := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp [Tt, taylor_coeff_zero]
    · simp [Tt, taylor_coeff_one]
  obtain ⟨U, hU⟩ := hdvd
  have hU0 : U.coeff 0 = (hasseDeriv 2 G).eval xa := by
    have := congrArg (fun p => p.coeff 2) hU
    simp only [coeff_sub, coeff_C, coeff_C_mul, coeff_X] at this
    have e : (X ^ 2 * U).coeff 2 = U.coeff 0 := by
      rw [show (2 : ℕ) = 0 + 2 by rfl, coeff_X_pow_mul]
    rw [e] at this
    rw [← this, hTt, taylor_coeff]
    simp
  refine ⟨C c + C g * X + X ^ 2 * U.comp (C 2 * X), ?_, ?_⟩
  · intro z
    have h1 := congrArg (eval (2 * z)) hU
    simp only [eval_sub, eval_C, eval_mul, eval_X, eval_pow, Tt, taylor_eval] at h1
    simp only [eval_add, eval_C, eval_mul, eval_X, eval_pow, eval_comp]
    rw [add_comm xa (2 * z)]
    rw [hc, hg] at h1
    linear_combination -h1
  · intro y
    have hmap : (C c + C g * X + X ^ 2 * U.comp (C 2 * X)).map S.π
        = C (S.π c) + C (S.π g) * X + X ^ 2 * C ((U.map S.π).eval 0) := by
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_pow, map_comp, S.pi_two, C_0, zero_mul, comp_zero]
    have hκ : (U.map S.π).eval 0 = S.π ((hasseDeriv 2 G).eval xa) := by
      rw [eval_map, eval₂_at_zero, hU0]
    rw [hmap, hκ]
    constructor
    · simp only [eval_add, eval_C, eval_mul, eval_X, eval_pow]; ring
    · simp only [derivative_add, derivative_C, derivative_mul, derivative_X, derivative_X_pow,
        eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero, eval_one]
      have : (2 : F) = 0 := S.two_F
      simp [this]

section card
variable [Fintype R] [DecidableEq R] [Fintype F] [DecidableEq F]

theorem class_count (hcard : Fintype.card R = Fintype.card F ^ S.k) (G : R[X]) (xa c g : R)
    (hc : G.eval xa = 4 * c) (hg : G.derivative.eval xa = 2 * g) (hgπ : S.π g ≠ 0) :
    (univ.filter (fun x : R => S.π x = S.π xa ∧ G.eval x = 0)).card =
      Fintype.card F * (univ.filter (fun y : F =>
        S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card := by
  obtain ⟨P, hP4, hPbar⟩ := S.exists_local_poly G xa c g hc hg
  have hsimple : ∀ t : F, (P.map S.π).eval t = 0 → (P.map S.π).derivative.eval t ≠ 0 := by
    intro t _; rw [(hPbar t).2]; exact hgπ
  have hk := S.hk
  have hTcard := S.card_T hcard P hsimple (S.k - 2) (by omega) (by omega)
  have hroots : univ.filter (fun t : F => (P.map S.π).eval t = 0) =
      univ.filter (fun y : F =>
        S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, (hPbar y).1]
  rw [hroots, show S.k - (S.k - 2) = 2 by omega] at hTcard
  -- T P (k-2) = {z : G(xa + 2z) = 0}
  have hT : ∀ z, z ∈ T P (S.k - 2) ↔ G.eval (xa + 2 * z) = 0 := by
    intro z
    rw [mem_T, ← hP4, S.four_mul_eq_zero_iff]
  -- fiberwise count along z ↦ xa + 2 z
  set C0 := univ.filter (fun x : R => S.π x = S.π xa ∧ G.eval x = 0) with hC0
  have key := Finset.card_eq_sum_card_fiberwise (s := T P (S.k - 2)) (t := C0)
    (f := fun z => xa + 2 * z) (fun z hz => by
      rw [Finset.mem_coe, hC0, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, (hT z).mp hz⟩
      rw [map_add, S.pi_two_mul, add_zero])
  have hfib : ∀ x ∈ C0, ((T P (S.k - 2)).filter (fun z => xa + 2 * z = x)).card = Fintype.card F := by
    intro x hx
    rw [hC0, Finset.mem_filter] at hx
    obtain ⟨-, hxa, hGx⟩ := hx
    have : S.π (x - xa) = 0 := by rw [map_sub, hxa, sub_self]
    obtain ⟨y0, hy0⟩ := (S.ker2 _).mp this
    rw [← S.card_ann_two hcard]
    apply Finset.card_bij (fun z _ => z - y0)
    · intro z hz
      rw [Finset.mem_filter] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hz.2
      linear_combination this + hy0
    · intro z _ w _ h; simpa using h
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨w + y0, ?_, by ring⟩
      rw [Finset.mem_filter, hT]
      constructor
      · have : xa + 2 * (w + y0) = x := by linear_combination hw - hy0
        rw [this]; exact hGx
      · linear_combination hw - hy0
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hTcard] at key
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have : (univ.filter (fun y : F =>
      S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card *
      Fintype.card F ^ 2 = (Fintype.card F * (univ.filter (fun y : F =>
      S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card) * Fintype.card F := by
    ring
  rw [this] at key
  exact (Nat.eq_of_mul_eq_mul_right hq key).symm

theorem class_count_zero (G : R[X]) (xa g : R) (hg : G.derivative.eval xa = 2 * g)
    (hnot : ¬ ∃ c, G.eval xa = 4 * c) :
    (univ.filter (fun x : R => S.π x = S.π xa ∧ G.eval x = 0)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hxa, hGx⟩
  have : S.π (x - xa) = 0 := by rw [map_sub, hxa, sub_self]
  obtain ⟨y, hy⟩ := (S.ker2 _).mp this
  obtain ⟨Q, hQ⟩ := taylor2 G xa (2 * y)
  have hx : x = xa + 2 * y := by linear_combination hy
  rw [← hx, hGx, hg] at hQ
  exact hnot ⟨-(y * g + y ^ 2 * Q), by linear_combination -hQ⟩

end card

end GRS

end APN2

#print axioms APN2.GRS.class_count
#print axioms APN2.GRS.class_count_zero
