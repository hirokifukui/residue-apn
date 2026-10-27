import Apn2R03.Bounds

/-!
# Independent control of A_F and E_F (Claude, 2026-10-25)

* `A_control`   : A_{f+2H} = A_f + D_ρ(H' mod 2)                         (F3(i))
* `exists_deriv_lift` : every function K → K is the residue of some H'   (F3(ii))
* `A_prescribe` : A_F can be made any ρ-periodic function                (F3)
* `E_control`   : E_{f+2J²} = E_f + (D_ρ j)², A unchanged                 (E6)
* `E_prescribe` : with A nowhere zero and μ ≠ 0, E can be moved off Im L_a on every Λ-zero pair
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

theorem map_add_two (f H : R[X]) : (f + C 2 * H).map S.π = f.map S.π := by
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, S.pi_two, C_0, zero_mul,
    add_zero]

theorem Lam_add_two (f H : R[X]) (ρ a : K) : S.Lam (f + C 2 * H) ρ a = S.Lam f ρ a := by
  unfold Lam; rw [S.map_add_two]

theorem hyp_add_two (f H : R[X]) (ρ μ : K) (h : S.Hyp f ρ μ) : S.Hyp (f + C 2 * H) ρ μ := by
  have e := S.map_add_two f H
  exact ⟨h.hρ, by rw [e]; exact h.hper, by rw [e]; exact h.hμ, by rw [e]; exact h.hdp⟩

theorem A_control (f H : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a) (a : K) :
    S.Afun (f + C 2 * H) ρ a = S.Afun f ρ a +
      ((H.derivative.map S.π).eval (a + ρ) - (H.derivative.map S.π).eval a) := by
  obtain ⟨g0, hg0⟩ := S.D_even f ρ hper (S.L a) (S.L ρ) (S.pi_L ρ)
  unfold Afun
  have hd : (f + C 2 * H).derivative = f.derivative + C 2 * H.derivative := by
    rw [derivative_add, derivative_C_mul]
  rw [hd, hg0, S.half_eq]
  have : (f.derivative + C 2 * H.derivative).eval (S.L a + S.L ρ) -
      (f.derivative + C 2 * H.derivative).eval (S.L a) =
      2 * (g0 + (H.derivative.eval (S.L a + S.L ρ) - H.derivative.eval (S.L a))) := by
    simp only [eval_add, eval_mul, eval_C]
    linear_combination hg0
  rw [this, S.half_eq, map_add, map_sub, S.pi_eval, S.pi_eval, map_add, S.pi_L, S.pi_L]

section fin
variable [Fintype K] [DecidableEq K]

theorem exists_interp (h : K → K) : ∃ P : K[X], ∀ a, P.eval a = h a := by
  refine ⟨Lagrange.interpolate univ id h, fun a => ?_⟩
  have := Lagrange.eval_interpolate_at_node (s := (univ : Finset K)) (v := id) h
    (Set.injOn_id _) (Finset.mem_univ a)
  simpa using this

theorem sq_injective (S : GRS R K) : Function.Injective (fun t : K => t ^ 2) := by
  intro t t' h
  simp only at h
  have h2 := S.two_F
  have : (t - t') ^ 2 = 0 := by linear_combination h + (t' ^ 2 - t * t') * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

theorem exists_sqrt (S : GRS R K) (u : K) : ∃ t : K, t ^ 2 = u :=
  (Finite.injective_iff_surjective.mp S.sq_injective) u

theorem exists_deriv_lift (h : K → K) : ∃ H : R[X], ∀ a, (H.derivative.map S.π).eval a = h a := by
  choose s hs using fun a => S.exists_sqrt (h a)
  obtain ⟨P, hP⟩ := exists_interp s
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective S.π S.surj P
  refine ⟨X * Q ^ 2, fun a => ?_⟩
  rw [← derivative_map, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_pow, hQ,
    derivative_mul, derivative_X, one_mul, derivative_sq]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, hP]
  have h2 := S.two_F
  rw [hs, h2]; ring

theorem A_prescribe (f : R[X]) (ρ : K) (hρ : ρ ≠ 0)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (φ : K → K) (hφ : ∀ a, φ (a + ρ) = φ a) :
    ∃ H : R[X], ∀ a, S.Afun (f + C 2 * H) ρ a = φ a := by
  have h2 := S.two_F
  have hρ2 : ρ + ρ = 0 := by linear_combination ρ * h2
  obtain ⟨h, hh⟩ := APN2R03.Drho_surj ρ hρ hρ2 (fun a => φ a - S.Afun f ρ a)
    (fun a => by rw [hφ, S.A_periodic f ρ hper])
  obtain ⟨H, hH⟩ := S.exists_deriv_lift h
  refine ⟨H, fun a => ?_⟩
  rw [S.A_control f H ρ hper, hH, hH]
  have := hh a
  linear_combination this - h a * h2

theorem E_control (f J : R[X]) (ρ : K) (a : K) (hL : S.Lam f ρ a = 0) :
    S.Efun (f + C 2 * J ^ 2) ρ a = S.Efun f ρ a +
      ((J.map S.π).eval (a + ρ) - (J.map S.π).eval a) ^ 2 := by
  set x := S.L a
  set τ := S.L ρ
  obtain ⟨c, hc⟩ := S.S_div4 f ρ x τ a (S.pi_L a) (S.pi_L ρ) hL
  obtain ⟨W, hW⟩ := taylor2 (J ^ 2) x (2 * τ)
  have hQd : (J ^ 2).derivative.eval x = 2 * (J.eval x * J.derivative.eval x) := by
    rw [derivative_sq]; simp; ring
  have hE0 : S.Efun f ρ a = S.π c := by
    unfold Efun; unfold Sx at hc; rw [hc, S.quarter_eq]
  have key : (f + C 2 * J ^ 2).eval (x + 2 * τ) - 2 * (f + C 2 * J ^ 2).eval (x + τ)
      + (f + C 2 * J ^ 2).eval x =
      4 * (c + ((J ^ 2).eval x - (J ^ 2).eval (x + τ)) + 2 * (τ * (J.eval x * J.derivative.eval x)
        + τ ^ 2 * W)) := by
    simp only [eval_add, eval_mul, eval_C]
    unfold Sx at hc
    rw [hW, hQd]
    linear_combination hc
  rw [hE0]
  unfold Efun
  rw [key, S.quarter_eq, map_add, map_add, map_sub, S.pi_two_mul, add_zero, S.pi_eval,
    S.pi_eval, map_add, S.pi_L, S.pi_L]
  simp only [Polynomial.map_pow, eval_pow]
  have h2 := S.two_F
  linear_combination (-(J.map S.π).eval (a + ρ) ^ 2 + (J.map S.π).eval (a + ρ) * (J.map S.π).eval a) * h2

theorem A_add_sq (f J : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a) (a : K) :
    S.Afun (f + C 2 * J ^ 2) ρ a = S.Afun f ρ a := by
  rw [S.A_control f (J ^ 2) ρ hper]
  have : ((J ^ 2).derivative.map S.π) = 0 := by
    rw [derivative_sq, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, S.pi_two, C_0,
      zero_mul, zero_mul]
  rw [this]; simp

/-- closure of the image of y ↦ μy²+Ay under addition (char 2) -/
theorem qimg_add (S : GRS R K) (μ A u v : K) (hu : u ∈ APN2R03.qimg μ A) (hv : v ∈ APN2R03.qimg μ A) :
    u + v ∈ APN2R03.qimg μ A := by
  haveI := S.charP2
  unfold APN2R03.qimg at *
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at *
  obtain ⟨y, rfl⟩ := hu
  obtain ⟨z, rfl⟩ := hv
  exact ⟨y + z, APN2R03.qmap_add μ A y z⟩

theorem exists_not_qimg (S : GRS R K) (m : ℕ) (hm : Fintype.card K = 2 ^ m) (μ A : K) (hμ : μ ≠ 0) (hA : A ≠ 0) :
    ∃ t, t ∉ APN2R03.qimg μ A := by
  haveI := S.charP2
  by_contra h
  simp only [not_exists, not_not] at h
  have hall : APN2R03.qimg μ A = univ := Finset.eq_univ_of_forall h
  have hc := APN2R03.card_qimg m hm μ A hμ hA
  rw [hall, Finset.card_univ, hm] at hc
  have hpos : 0 < 2 ^ m := by positivity
  omega

theorem E_prescribe (m : ℕ) (hm : Fintype.card K = 2 ^ m) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0) (hA : ∀ a, S.Afun f ρ a ≠ 0) :
    ∃ J : R[X], (∀ a, S.Afun (f + C 2 * J ^ 2) ρ a = S.Afun f ρ a) ∧
      ∀ a, S.Lam (f + C 2 * J ^ 2) ρ a = 0 →
        S.Efun (f + C 2 * J ^ 2) ρ a ∉ APN2R03.qimg μ (S.Afun f ρ (a)) := by
  classical
  haveI := S.charP2
  have h2 := S.two_F
  have hρ2 : ρ + ρ = 0 := by linear_combination ρ * h2
  have hex : ∀ A : K, A ≠ 0 → ∃ t, t ∉ APN2R03.qimg μ A :=
    fun A hA' => S.exists_not_qimg m hm μ A hμ0 hA'
  let tA : K → K := fun A => if h : A ≠ 0 then (hex A h).choose else 0
  have htA : ∀ A, A ≠ 0 → tA A ∉ APN2R03.qimg μ A := by
    intro A h; simp only [tA, dif_pos h]; exact (hex A h).choose_spec
  let P : K → Prop := fun a => S.Lam f ρ a = 0 ∧ S.Efun f ρ a ∈ APN2R03.qimg μ (S.Afun f ρ a)
  have hLρ : ∀ a, S.Lam f ρ a = 0 → S.Efun f ρ (a + ρ) = S.Efun f ρ a +
      (μ * ρ ^ 2 + S.Afun f ρ a * ρ) := by
    intro a hL
    have := S.E_transl f ρ μ H.hper H.hμ a hL
    linear_combination this - S.Efun f ρ a * h2
  have hLimg : ∀ a, (μ * ρ ^ 2 + S.Afun f ρ a * ρ) ∈ APN2R03.qimg μ (S.Afun f ρ a) := by
    intro a; unfold APN2R03.qimg; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨ρ, rfl⟩
  have hPper : ∀ a, P (a + ρ) ↔ P a := by
    intro a
    simp only [P, S.Lam_periodic f ρ H.hper, S.A_periodic f ρ H.hper]
    constructor
    · rintro ⟨hL, hE⟩
      refine ⟨hL, ?_⟩
      rw [hLρ a hL] at hE
      have := S.qimg_add μ _ _ _ hE (hLimg a)
      have e : S.Efun f ρ a + (μ * ρ ^ 2 + S.Afun f ρ a * ρ) + (μ * ρ ^ 2 + S.Afun f ρ a * ρ) =
          S.Efun f ρ a := by linear_combination (μ * ρ ^ 2 + S.Afun f ρ a * ρ) * h2
      rwa [e] at this
    · rintro ⟨hL, hE⟩
      exact ⟨hL, by rw [hLρ a hL]; exact S.qimg_add μ _ _ _ hE (hLimg a)⟩
  let d : K → K := fun a => if P a then tA (S.Afun f ρ a) else 0
  have hd : ∀ a, d (a + ρ) = d a := by
    intro a
    by_cases hp : P a
    · have hp' : P (a + ρ) := (hPper a).mpr hp
      simp only [d, if_pos hp, if_pos hp', S.A_periodic f ρ H.hper]
    · have hp' : ¬ P (a + ρ) := fun h => hp ((hPper a).mp h)
      simp only [d, if_neg hp, if_neg hp']
  choose sq hsq using fun a => S.exists_sqrt (d a)
  have hsqper : ∀ a, sq (a + ρ) = sq a := by
    intro a; apply S.sq_injective; simp only; rw [hsq, hsq, hd]
  obtain ⟨j0, hj0⟩ := APN2R03.Drho_surj ρ H.hρ hρ2 sq hsqper
  obtain ⟨P0, hP0⟩ := exists_interp j0
  obtain ⟨J, hJ⟩ := Polynomial.map_surjective S.π S.surj P0
  refine ⟨J, fun a => S.A_add_sq f J ρ H.hper a, fun a hL => ?_⟩
  rw [S.Lam_add_two] at hL
  rw [S.E_control f J ρ a hL, hJ, hP0, hP0]
  have hj : j0 (a + ρ) - j0 a = sq a := by linear_combination hj0 a - j0 a * h2
  rw [hj, hsq]
  by_cases hp : P a
  · simp only [d, if_pos hp]
    intro hmem
    apply htA _ (hA a)
    have := S.qimg_add μ _ _ _ hmem hp.2
    have e : S.Efun f ρ a + tA (S.Afun f ρ a) + S.Efun f ρ a = tA (S.Afun f ρ a) := by
      linear_combination (S.Efun f ρ a) * h2
    rwa [e] at this
  · simp only [d, if_neg hp, add_zero]
    intro hmem
    exact hp ⟨hL, hmem⟩

end fin

end GRS

end APN2

#print axioms APN2.GRS.A_prescribe
#print axioms APN2.GRS.E_control
#print axioms APN2.GRS.E_prescribe
