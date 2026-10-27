import Apn2R03.Local

/-!
# Lift invariants A_F and E_F (Claude, 2026-10-25)

Notation: `f : R[X]` is the lift, `p = f.map π`, `ρ ∈ K`.
* `Afun` : A_F(a) = residue of (f'(x+τ) − f'(x))/2   (F2: lift independent, ρ-periodic)
* `Lam`  : Λ(a) = p(a+ρ) − p(a) − ρ p'(a)
* `Efun` : E_F(a) = residue of (f(x+2τ) − 2f(x+τ) + f(x))/4 on Λ = 0   (E1, E2)
* `E_transl` : E(a+ρ) + E(a) = ρ A(a) + ρ² μ   (E3)
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

theorem hasse_comp_eval {R : Type*} [CommRing R] (f : R[X]) (a x : R) (n : ℕ) :
    (hasseDeriv n (f.comp (X + C a))).eval x = (hasseDeriv n f).eval (x + a) := by
  rw [← taylor_coeff, ← taylor_coeff]
  congr 1
  simp only [taylor_apply, comp_assoc]
  congr 1
  simp only [add_comp, X_comp, C_comp, C_add]
  ring

theorem eval_comp_add {R : Type*} [CommRing R] (f : R[X]) (a x : R) :
    (f.comp (X + C a)).eval x = f.eval (x + a) := by
  simp [eval_comp]

theorem deriv_comp_add {R : Type*} [CommRing R] (f : R[X]) (a : R) :
    (f.comp (X + C a)).derivative = f.derivative.comp (X + C a) := by
  rw [derivative_comp]; simp

theorem deriv2_eval {R : Type*} [CommRing R] (f : R[X]) (x : R) :
    (f.derivative.derivative).eval x = 2 * (hasseDeriv 2 f).eval x := by
  have h := factorial_smul_hasseDeriv (R := R) 2
  have h2 : derivative (derivative f) = (2 : ℕ) • hasseDeriv 2 f := by
    have := congrArg (fun φ => φ f) h
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at this
    rw [← this]; simp [Nat.factorial]
  rw [h2]; simp [nsmul_eq_mul]

/-- f'(x + 2u) ≡ f'(x) (mod 4) -/
theorem dmod4 {R : Type*} [CommRing R] (f : R[X]) (x u : R) :
    ∃ w, f.derivative.eval (x + 2 * u) = f.derivative.eval x + 4 * w := by
  obtain ⟨Q, hQ⟩ := taylor2 f.derivative x (2 * u)
  refine ⟨u * (hasseDeriv 2 f).eval x + u ^ 2 * Q, ?_⟩
  rw [hQ, deriv2_eval]; ring

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

/-- a fixed lift of residues -/
noncomputable def L (a : K) : R := Function.surjInv S.surj a

theorem pi_L (a : K) : S.π (S.L a) = a := Function.surjInv_eq S.surj a

theorem sub_two_of_pi_eq {y y' : R} (h : S.π y = S.π y') : ∃ z, y - y' = 2 * z := by
  apply (S.ker2 _).mp; rw [map_sub, h, sub_self]

theorem neg_eq_self_K (S : GRS R K) (y : K) : -y = y := by
  have h2 := S.two_F
  linear_combination -y * h2

theorem sub_eq_add_K (S : GRS R K) (y z : K) : y - z = y + z := by
  rw [sub_eq_add_neg, S.neg_eq_self_K]

/-- A_F -/
noncomputable def Afun (f : R[X]) (ρ : K) (a : K) : K :=
  S.half (f.derivative.eval (S.L a + S.L ρ) - f.derivative.eval (S.L a))

/-- Λ -/
noncomputable def Lam (f : R[X]) (ρ : K) (a : K) : K :=
  (f.map S.π).eval (a + ρ) - (f.map S.π).eval a - ρ * (f.map S.π).derivative.eval a

/-- E_F -/
noncomputable def Efun (f : R[X]) (ρ : K) (a : K) : K :=
  S.quarter (f.eval (S.L a + 2 * S.L ρ) - 2 * f.eval (S.L a + S.L ρ) + f.eval (S.L a))

theorem pi_D (f : R[X]) (x τ : R) :
    S.π (f.derivative.eval (x + τ) - f.derivative.eval x) =
      (f.map S.π).derivative.eval (S.π x + S.π τ) - (f.map S.π).derivative.eval (S.π x) := by
  rw [map_sub, S.pi_deriv_eval, S.pi_deriv_eval, map_add]

theorem D_even (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (x τ : R) (hτ : S.π τ = ρ) : ∃ g, f.derivative.eval (x + τ) - f.derivative.eval x = 2 * g := by
  apply (S.ker2 _).mp
  rw [S.pi_D, hτ, hper, sub_self]

/-- F2: lift independence of A_F -/
theorem A_spec (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (x τ : R) (a : K) (hx : S.π x = a) (hτ : S.π τ = ρ) :
    ∃ g, f.derivative.eval (x + τ) - f.derivative.eval x = 2 * g ∧ S.π g = S.Afun f ρ a := by
  obtain ⟨g, hg⟩ := S.D_even f ρ hper x τ hτ
  refine ⟨g, hg, ?_⟩
  obtain ⟨g0, hg0⟩ := S.D_even f ρ hper (S.L a) (S.L ρ) (S.pi_L ρ)
  unfold Afun
  rw [hg0, S.half_eq]
  -- compare the two differences modulo 4
  obtain ⟨u, hu⟩ := S.sub_two_of_pi_eq (y := x) (y' := S.L a) (by rw [hx, S.pi_L])
  obtain ⟨v, hv⟩ := S.sub_two_of_pi_eq (y := τ) (y' := S.L ρ) (by rw [hτ, S.pi_L])
  have ex : x = S.L a + 2 * u := by linear_combination hu
  have eτ : x + τ = (S.L a + S.L ρ) + 2 * (u + v) := by linear_combination hu + hv
  obtain ⟨w1, hw1⟩ := dmod4 f (S.L a + S.L ρ) (u + v)
  obtain ⟨w2, hw2⟩ := dmod4 f (S.L a) u
  have : 2 * g = 2 * (g0 + 2 * (w1 - w2)) := by
    rw [← hg, eτ, ex, hw1, hw2]
    linear_combination hg0
  have h := S.pi_eq_of_two_mul_eq this
  rw [h, map_add, S.pi_two_mul, add_zero]

theorem A_periodic (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a) (a : K) :
    S.Afun f ρ (a + ρ) = S.Afun f ρ a := by
  obtain ⟨g1, hg1, hπ1⟩ := S.A_spec f ρ hper (S.L a) (S.L ρ) a (S.pi_L a) (S.pi_L ρ)
  obtain ⟨g2, hg2, hπ2⟩ := S.A_spec f ρ hper (S.L a + S.L ρ) (S.L ρ) (a + ρ)
    (by rw [map_add, S.pi_L, S.pi_L]) (S.pi_L ρ)
  obtain ⟨w, hw⟩ := dmod4 f (S.L a) (S.L ρ)
  have : 2 * (g1 + g2) = 2 * (2 * w) := by
    have e : S.L a + S.L ρ + S.L ρ = S.L a + 2 * S.L ρ := by ring
    rw [e] at hg2
    linear_combination -(hg1 + hg2) + hw
  have h := S.pi_eq_of_two_mul_eq this
  rw [map_add, hπ1, hπ2, S.pi_two_mul] at h
  linear_combination h - (S.Afun f ρ a) * S.two_F


/-- second difference S(x) = f(x+2τ) − 2 f(x+τ) + f(x) -/
def Sx (f : R[X]) (x τ : R) : R := f.eval (x + 2 * τ) - 2 * f.eval (x + τ) + f.eval x

theorem pi_hasse2_eval (f : R[X]) (y : R) :
    S.π ((hasseDeriv 2 f).eval y) = (hasseDeriv 2 (f.map S.π)).eval (S.π y) := by
  rw [S.pi_eval]
  congr 1
  ext n
  simp [hasseDeriv_coeff, coeff_map]

/-- E1: the numerator is divisible by 4 on Λ = 0 -/
theorem S_div4 (f : R[X]) (ρ : K) (x τ : R) (a : K) (hx : S.π x = a) (hτ : S.π τ = ρ)
    (hL : S.Lam f ρ a = 0) : ∃ c, Sx f x τ = 4 * c := by
  obtain ⟨Q1, hQ1⟩ := taylor2 f x (2 * τ)
  obtain ⟨Q2, hQ2⟩ := taylor2 f x τ
  have hπ : S.π (τ ^ 2 * Q2) = 0 := by
    have e : τ ^ 2 * Q2 = f.eval (x + τ) - f.eval x - τ * f.derivative.eval x := by
      rw [hQ2]; ring
    rw [e, map_sub, map_sub, map_mul, S.pi_eval, S.pi_eval, S.pi_deriv_eval, map_add, hx, hτ]
    exact hL
  obtain ⟨y, hy⟩ := (S.ker2 _).mp hπ
  refine ⟨τ ^ 2 * Q1 - y, ?_⟩
  unfold Sx
  rw [hQ1, hQ2]
  linear_combination -2 * hy

/-- change of τ by 2v changes S by a multiple of 8 -/
theorem S_tau_change (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (x τ v : R) (hτ : S.π τ = ρ) : ∃ w, Sx f x (τ + 2 * v) = Sx f x τ + 8 * w := by
  obtain ⟨Q, hQ⟩ := taylor2 f (x + 2 * τ) (4 * v)
  obtain ⟨Q', hQ'⟩ := taylor2 f (x + τ) (2 * v)
  obtain ⟨g, hg⟩ := S.D_even f ρ hper (x + τ) τ hτ
  refine ⟨v * g + 2 * v ^ 2 * Q - v ^ 2 * Q', ?_⟩
  unfold Sx
  have e1 : x + 2 * (τ + 2 * v) = (x + 2 * τ) + 4 * v := by ring
  have e2 : x + (τ + 2 * v) = (x + τ) + 2 * v := by ring
  have e3 : x + τ + τ = x + 2 * τ := by ring
  rw [e1, e2, hQ, hQ']
  rw [e3] at hg
  linear_combination 4 * v * hg

/-- change of x by 2u changes S by a multiple of 8 -/
theorem S_x_change (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (x τ u : R) (hτ : S.π τ = ρ) : ∃ w, Sx f (x + 2 * u) τ = Sx f x τ + 8 * w := by
  set Sp := f.comp (X + C (2 * τ)) - f.comp (X + C τ) - f.comp (X + C τ) + f with hSp
  have hev : ∀ y, Sp.eval y = Sx f y τ := by
    intro y; simp only [Sp, eval_add, eval_sub, eval_comp_add, Sx]; ring
  obtain ⟨Q, hQ⟩ := taylor3 Sp x (2 * u)
  have hd : Sp.derivative.eval x =
      f.derivative.eval (x + 2 * τ) - f.derivative.eval (x + τ) - f.derivative.eval (x + τ)
        + f.derivative.eval x := by
    simp only [Sp, derivative_add, derivative_sub, deriv_comp_add, eval_add, eval_sub,
      eval_comp_add]
  have hh : (hasseDeriv 2 Sp).eval x =
      (hasseDeriv 2 f).eval (x + 2 * τ) - (hasseDeriv 2 f).eval (x + τ)
        - (hasseDeriv 2 f).eval (x + τ) + (hasseDeriv 2 f).eval x := by
    simp only [Sp, map_add, map_sub, eval_add, eval_sub, hasse_comp_eval]
  obtain ⟨w4, hw4⟩ := dmod4 f x τ
  obtain ⟨g, hg⟩ := S.D_even f ρ hper x τ hτ
  obtain ⟨z, hz⟩ := S.sub_two_of_pi_eq (y := (hasseDeriv 2 f).eval (x + 2 * τ))
    (y' := (hasseDeriv 2 f).eval x) (by rw [S.pi_hasse2_eval, S.pi_hasse2_eval, map_add,
      S.pi_two_mul, add_zero])
  refine ⟨u * (w4 - g) + u ^ 2 * ((hasseDeriv 2 f).eval x - (hasseDeriv 2 f).eval (x + τ) + z)
    + u ^ 3 * Q, ?_⟩
  rw [← hev, ← hev, hQ, hd, hh]
  linear_combination 2 * u * hw4 - 4 * u * hg + 4 * u ^ 2 * hz

/-- E2: lift independence of E_F -/
theorem E_spec (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (x τ : R) (a : K) (hx : S.π x = a) (hτ : S.π τ = ρ) (hL : S.Lam f ρ a = 0) :
    ∃ c, Sx f x τ = 4 * c ∧ S.π c = S.Efun f ρ a := by
  obtain ⟨c0, hc0⟩ := S.S_div4 f ρ (S.L a) (S.L ρ) a (S.pi_L a) (S.pi_L ρ) hL
  obtain ⟨u, hu⟩ := S.sub_two_of_pi_eq (y := x) (y' := S.L a) (by rw [hx, S.pi_L])
  obtain ⟨v, hv⟩ := S.sub_two_of_pi_eq (y := τ) (y' := S.L ρ) (by rw [hτ, S.pi_L])
  have ex : x = S.L a + 2 * u := by linear_combination hu
  have eτ : τ = S.L ρ + 2 * v := by linear_combination hv
  obtain ⟨w1, hw1⟩ := S.S_tau_change f ρ hper (S.L a + 2 * u) (S.L ρ) v (S.pi_L ρ)
  obtain ⟨w2, hw2⟩ := S.S_x_change f ρ hper (S.L a) (S.L ρ) u (S.pi_L ρ)
  refine ⟨c0 + 2 * (w1 + w2), ?_, ?_⟩
  · rw [ex, eτ, hw1, hw2, hc0]; ring
  · have hE : S.Efun f ρ a = S.π c0 := by
      unfold Efun
      have : f.eval (S.L a + 2 * S.L ρ) - 2 * f.eval (S.L a + S.L ρ) + f.eval (S.L a) = 4 * c0 := hc0
      rw [this, S.quarter_eq]
    rw [hE, map_add, S.pi_two_mul, add_zero]

theorem Lam_periodic (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a) (a : K) :
    S.Lam f ρ (a + ρ) = S.Lam f ρ a := by
  unfold Lam
  have h2 := S.two_F
  have e : a + ρ + ρ = a := by linear_combination ρ * h2
  rw [e, hper]
  linear_combination ((f.map S.π).eval a - (f.map S.π).eval (a + ρ)) * h2

/-- E3: translation identity E(a+ρ) + E(a) = ρ A(a) + ρ² μ -/
theorem E_transl (f : R[X]) (ρ μ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (hμ : ∀ a, (hasseDeriv 2 (f.map S.π)).eval (a + ρ) - (hasseDeriv 2 (f.map S.π)).eval a = μ)
    (a : K) (hL : S.Lam f ρ a = 0) :
    S.Efun f ρ (a + ρ) + S.Efun f ρ a = ρ * S.Afun f ρ a + ρ ^ 2 * μ := by
  set x := S.L a
  set τ := S.L ρ
  have hx : S.π x = a := S.pi_L a
  have hτ : S.π τ = ρ := S.pi_L ρ
  obtain ⟨c1, hc1, hπ1⟩ := S.E_spec f ρ hper (x + τ) τ (a + ρ) (by rw [map_add, hx, hτ]) hτ
    (by rw [S.Lam_periodic f ρ hper]; exact hL)
  obtain ⟨c0, hc0, hπ0⟩ := S.E_spec f ρ hper x τ a hx hτ hL
  obtain ⟨g, hg, hπg⟩ := S.A_spec f ρ hper x τ a hx hτ
  set Gp := f.comp (X + C τ) - f with hGp
  obtain ⟨Q, hQ⟩ := taylor3 Gp x (2 * τ)
  have hG : ∀ y, Gp.eval y = f.eval (y + τ) - f.eval y := by
    intro y; simp [Gp]
  have hGd : Gp.derivative.eval x = f.derivative.eval (x + τ) - f.derivative.eval x := by
    simp [Gp, deriv_comp_add]
  have hGh : (hasseDeriv 2 Gp).eval x = (hasseDeriv 2 f).eval (x + τ) - (hasseDeriv 2 f).eval x := by
    simp only [Gp, map_sub, eval_sub, hasse_comp_eval]
  rw [hG, hG, hGd, hGh, hg] at hQ
  have hsum : 4 * (c1 + c0) = 4 * (τ * g + τ ^ 2 * ((hasseDeriv 2 f).eval (x + τ)
      - (hasseDeriv 2 f).eval x) + 2 * τ ^ 3 * Q) := by
    unfold Sx at hc1 hc0
    have e1 : x + τ + 2 * τ = x + 2 * τ + τ := by ring
    have e2 : x + τ + τ = x + 2 * τ := by ring
    rw [e1, e2] at hc1
    linear_combination -hc1 - hc0 + hQ
  have h := S.pi_eq_of_four_mul_eq hsum
  rw [map_add, hπ1, hπ0] at h
  rw [h, map_add, map_add, map_mul, map_mul, map_pow, map_sub, S.pi_hasse2_eval, S.pi_hasse2_eval,
    map_add, hx, hτ, hμ, hπg, map_mul, map_mul, S.pi_two, zero_mul, zero_mul, add_zero]

end GRS

end APN2

#print axioms APN2.GRS.A_spec
#print axioms APN2.GRS.E_spec
#print axioms APN2.GRS.E_transl

