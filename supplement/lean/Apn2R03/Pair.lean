import Apn2R03.Invariants
import Apn2R03.Lemmas2

/-!
# Exceptional rows reduce to one residue pair (Claude, 2026-10-25)

For an exceptional direction α (π α = ρ) and β ∈ R:
* `delta_eq_sum`  : δ(α,β) = Σ_a #{x : π x = a, G(x) = 0},  G(X) = f(X+α) − f(X) − β;
* `delta_pair`    : only the pair {a₀, a₀+ρ} with D_ρ p(a₀) = β̄ contributes;
* `cc_formula`    : on a class with A(a) ≠ 0 the count is q · #{y : c + A y + μ y² = 0};
* `cc_shift`      : on a Λ-zero pair the constant of the second class is c + E(a).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

/-- G(X) = f(X+α) − f(X) − β -/
noncomputable def Gpoly (f : R[X]) (α β : R) : R[X] := f.comp (X + C α) - f - C β

theorem Gpoly_eval (f : R[X]) (α β x : R) :
    (Gpoly f α β).eval x = f.eval (x + α) - f.eval x - β := by
  simp [Gpoly]

theorem Gpoly_deriv_eval (f : R[X]) (α β x : R) :
    (Gpoly f α β).derivative.eval x = f.derivative.eval (x + α) - f.derivative.eval x := by
  simp [Gpoly, deriv_comp_add]

theorem Gpoly_hasse2_eval (f : R[X]) (α β x : R) :
    (hasseDeriv 2 (Gpoly f α β)).eval x = (hasseDeriv 2 f).eval (x + α) - (hasseDeriv 2 f).eval x := by
  simp only [Gpoly, map_sub, eval_sub, hasse_comp_eval]
  have : (hasseDeriv 2 (C β)).eval x = 0 := by
    rw [hasseDeriv_C _ _ (by norm_num)]; simp
  rw [this, sub_zero]

section card
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- δ_F(α, β) -/
def delta (f : R[X]) (α β : R) : ℕ := (univ.filter (fun x : R => f.eval (x + α) - f.eval x = β)).card

/-- count on one residue class -/
noncomputable def cc (f : R[X]) (α β : R) (a : K) : ℕ :=
  (univ.filter (fun x : R => S.π x = a ∧ (Gpoly f α β).eval x = 0)).card

theorem delta_eq_sum (f : R[X]) (α β : R) : delta f α β = ∑ a : K, S.cc f α β a := by
  unfold delta cc
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => S.π x) (t := (univ : Finset K))
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Gpoly_eval]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [h1]; ring⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linear_combination h2, h1⟩

/-- a class can only contribute when D_ρ p(a) = β̄ -/
theorem cc_gate (f : R[X]) (α β : R) (a : K) (h : S.cc f α β a ≠ 0) :
    (f.map S.π).eval (a + S.π α) - (f.map S.π).eval a = S.π β := by
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hxa, hG⟩ := hx
  have := congrArg S.π hG
  rw [Gpoly_eval, map_sub, map_sub, S.pi_eval, S.pi_eval, map_add, hxa, map_zero] at this
  linear_combination this

theorem delta_pair (f : R[X]) (α β : R) (ρ : K) (hα : S.π α = ρ) (hρ : ρ ≠ 0)
    (hdp : ∀ a b : K, (f.map S.π).eval (a + ρ) - (f.map S.π).eval a =
      (f.map S.π).eval (b + ρ) - (f.map S.π).eval b ↔ (b = a ∨ b = a + ρ))
    (a0 : K) (ha0 : (f.map S.π).eval (a0 + ρ) - (f.map S.π).eval a0 = S.π β) :
    delta f α β = S.cc f α β a0 + S.cc f α β (a0 + ρ) := by
  rw [S.delta_eq_sum]
  have hne : a0 ≠ a0 + ρ := by
    intro h; apply hρ; linear_combination -h
  apply Finset.sum_eq_add a0 (a0 + ρ) hne
  · intro b _ hb
    by_contra hc
    have hg := S.cc_gate f α β b hc
    rw [hα] at hg
    rcases (hdp a0 b).mp (by rw [ha0, hg]) with h | h
    · exact hb.1 h
    · exact hb.2 h
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem delta_no_pair (f : R[X]) (α β : R)
    (h : ∀ a : K, (f.map S.π).eval (a + S.π α) - (f.map S.π).eval a ≠ S.π β) :
    delta f α β = 0 := by
  rw [S.delta_eq_sum]
  apply Finset.sum_eq_zero
  intro a _
  by_contra hc
  exact h a (S.cc_gate f α β a hc)

theorem cc_zero (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (α β xa : R) (hα : S.π α = ρ)
    (hnot : ¬ ∃ c, (Gpoly f α β).eval xa = 4 * c) : S.cc f α β (S.π xa) = 0 := by
  obtain ⟨g, hg⟩ := S.D_even f ρ hper xa α hα
  exact S.class_count_zero (Gpoly f α β) xa g (by rw [Gpoly_deriv_eval]; exact hg) hnot

theorem cc_formula (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (hμ : ∀ a, (hasseDeriv 2 (f.map S.π)).eval (a + ρ) - (hasseDeriv 2 (f.map S.π)).eval a = μ)
    (α β xa c : R) (hα : S.π α = ρ) (hc : (Gpoly f α β).eval xa = 4 * c)
    (hA : S.Afun f ρ (S.π xa) ≠ 0) :
    S.cc f α β (S.π xa) = Fintype.card K *
      (univ.filter (fun y : K => S.π c + S.Afun f ρ (S.π xa) * y + μ * y ^ 2 = 0)).card := by
  obtain ⟨g, hg, hπg⟩ := S.A_spec f ρ hper xa α (S.π xa) rfl hα
  have h := S.class_count hcard (Gpoly f α β) xa c g hc (by rw [Gpoly_deriv_eval]; exact hg)
    (by rw [hπg]; exact hA)
  have hh : S.π ((hasseDeriv 2 (Gpoly f α β)).eval xa) = μ := by
    rw [Gpoly_hasse2_eval, map_sub, S.pi_hasse2_eval, S.pi_hasse2_eval, map_add, hα, hμ]
  rw [hh, hπg] at h
  exact h

/-- on a Λ-zero pair, the second class has constant c + E(a) when x_{a+ρ} = x_a + α -/
theorem cc_shift (f : R[X]) (ρ : K)
    (hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (α β xa c : R) (hα : S.π α = ρ) (hL : S.Lam f ρ (S.π xa) = 0)
    (hc : (Gpoly f α β).eval xa = 4 * c) :
    ∃ c', (Gpoly f α β).eval (xa + α) = 4 * c' ∧ S.π c' = S.π c + S.Efun f ρ (S.π xa) := by
  obtain ⟨e, he, hπe⟩ := S.E_spec f ρ hper xa α (S.π xa) rfl hα hL
  refine ⟨c + e, ?_, by rw [map_add, hπe]⟩
  rw [Gpoly_eval]
  rw [Gpoly_eval] at hc
  unfold Sx at he
  have e1 : xa + α + α = xa + 2 * α := by ring
  rw [e1]
  linear_combination hc + he

/-- the second class fails the gate when Λ(a) ≠ 0 and the first passes -/
theorem gate_exclusive (f : R[X]) (ρ : K)
    (_hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a)
    (α β xa c : R) (hα : S.π α = ρ) (hL : S.Lam f ρ (S.π xa) ≠ 0)
    (hc : (Gpoly f α β).eval xa = 4 * c) :
    ¬ ∃ c', (Gpoly f α β).eval (xa + α) = 4 * c' := by
  rintro ⟨c', hc'⟩
  obtain ⟨Q1, hQ1⟩ := taylor2 f xa (2 * α)
  obtain ⟨Q2, hQ2⟩ := taylor2 f xa α
  apply hL
  -- S(xa) = 4(c' - c) and S ≡ -2(f(x+α) - f(x) - α f'(x)) mod 4
  have hS : f.eval (xa + 2 * α) - 2 * f.eval (xa + α) + f.eval xa = 4 * (c' - c) := by
    rw [Gpoly_eval] at hc hc'
    have e1 : xa + α + α = xa + 2 * α := by ring
    rw [e1] at hc'
    linear_combination hc' - hc
  rw [hQ1, hQ2] at hS
  -- 2 α² Q2 = 4(α² Q1 - (c' - c))
  have h2 : 2 * (α ^ 2 * Q2) = 2 * (2 * (α ^ 2 * Q1 - (c' - c))) := by linear_combination -hS
  have := S.pi_eq_of_two_mul_eq h2
  rw [S.pi_two_mul] at this
  have e : α ^ 2 * Q2 = f.eval (xa + α) - f.eval xa - α * f.derivative.eval xa := by
    rw [hQ2]; ring
  rw [e, map_sub, map_sub, map_mul, S.pi_eval, S.pi_eval, S.pi_deriv_eval, map_add, hα] at this
  exact this

end card

end GRS

end APN2

#print axioms APN2.GRS.delta_pair
#print axioms APN2.GRS.cc_formula
#print axioms APN2.GRS.cc_shift
#print axioms APN2.GRS.gate_exclusive
