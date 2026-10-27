import Apn2R03.Family5b

/-!
# Ordinary unit directions (F1) and the full unit-direction statement of Theorem A (Claude, 2026-10-25)

F1: if π α = c and the residue derivative difference p'(t+c) − p'(t) never vanishes, every residue
root of D_c p − β̄ is simple, so δ_F(α, β) = #{t : D_c p(t) = β̄} (Hensel, `card_T` with j = k).
If p is APN this is ≤ 2.  For P_{m,r} the non-vanishing follows from ker = {0, 1}.  Here the APN
property of the residue permutation is an explicit input `hAPN`; it is discharged in `ResAPN.lean`
(`resAPN3`, `resAPN5`, wrappers `fam3_units'`, `fam5_units'`) from the form of the earlier paper
(arXiv:2610.21178, Thm 3.1): P_{m,r} = σ^{m-2} ∘ X³ ∘ T_r, T_r = Σ_{i<r} X^{2^i}, r is not a Gold
exponent; APN-ness of the cube, invertibility of T_r and the Frobenius identity give `ResAPN`.
(R04 correction: the earlier comment "linear equivalence with x^{2^r+1}" was wrong.)
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem map_Gpoly (f : R[X]) (α β : R) :
    (Gpoly f α β).map S.π = Gpoly (f.map S.π) (S.π α) (S.π β) := by
  simp [Gpoly, Polynomial.map_sub, Polynomial.map_comp]

/-- **F1** (ordinary directions): simple residue roots ⇒ δ equals the residue count. -/
theorem ordinary_eq (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (α β : R)
    (hsimple : ∀ t : K, (f.map S.π).derivative.eval (t + S.π α) ≠ (f.map S.π).derivative.eval t) :
    delta f α β =
      (univ.filter (fun t : K => (f.map S.π).eval (t + S.π α) - (f.map S.π).eval t = S.π β)).card := by
  have hT := S.card_T hcard (Gpoly f α β)
    (fun t _ => by rw [S.map_Gpoly, Gpoly_deriv_eval]; exact sub_ne_zero.mpr (hsimple t))
    S.k (by have := S.hk; omega) le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hT
  have e1 : delta f α β = (T (Gpoly f α β) S.k).card := by
    unfold delta; congr 1; ext x
    simp only [mem_filter, mem_univ, true_and, mem_T, Gpoly_eval, S.nil, zero_mul, exists_const]
    exact ⟨fun h => by rw [h, sub_self], fun h => sub_eq_zero.mp h⟩
  have e2 : univ.filter (fun t : K => ((Gpoly f α β).map S.π).eval t = 0) =
      univ.filter (fun t : K => (f.map S.π).eval (t + S.π α) - (f.map S.π).eval t = S.π β) := by
    ext t; simp only [mem_filter, mem_univ, true_and, S.map_Gpoly, Gpoly_eval, sub_eq_zero]
  rw [e1, hT, e2]

theorem ordinary_le (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (α β : R)
    (hsimple : ∀ t : K, (f.map S.π).derivative.eval (t + S.π α) ≠ (f.map S.π).derivative.eval t)
    (hapn : (univ.filter (fun t : K =>
      (f.map S.π).eval (t + S.π α) - (f.map S.π).eval t = S.π β)).card ≤ 2) :
    delta f α β ≤ 2 := by
  rw [S.ordinary_eq hcard f α β hsimple]; exact hapn

/-- residue APN property of p in all nonzero directions (input hypothesis) -/
def ResAPN (p : K[X]) : Prop :=
  ∀ c : K, c ≠ 0 → ∀ b : K, (univ.filter (fun t : K => p.eval (t + c) - p.eval t = b)).card ≤ 2

/-- **Theorem A (r = 3), all unit directions**: given that the residue polynomial is APN, every
entry δ_{F♯}(α, β) with π α ≠ 0 is at most 2q (and at most 2 off the exceptional direction). -/
theorem fam3_units (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ) (hm5 : 5 ≤ m)
    (hodd : Odd m) (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m)
    (hAPN : ResAPN (Fnat3 K m)) (α β : R) (hα : S.π α ≠ 0) :
    delta (Fsh3 R m) α β ≤ 2 * Fintype.card K ∧ (S.π α ≠ 1 → delta (Fsh3 R m) α β ≤ 2) := by
  haveI := S.charP2
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have hord : S.π α ≠ 1 → delta (Fsh3 R m) α β ≤ 2 := by
    intro h1
    apply S.ordinary_le hcard
    · intro t ht
      rw [S.fam3_sh_map, p3_deriv_add m (by omega) t (S.π α)] at ht
      have hk : (Fnat3 K m).derivative.eval (S.π α) = (Fnat3 K m).derivative.eval 0 := by
        linear_combination ht
      rcases (p3_ker m hm5 hm h3 _).mp hk with h | h
      · exact hα h
      · exact h1 h
    · rw [S.fam3_sh_map]; exact hAPN _ hα _
  refine ⟨?_, hord⟩
  by_cases h1 : S.π α = 1
  · exact S.fam3_upper hcard m hm5 hodd hm h3 α β h1
  · exact (hord h1).trans (by omega)

/-- **Theorem A (r ≥ 5), all unit directions.** -/
theorem fam5_units (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (hAPN : ResAPN (F5 K m r)) (α β : R) (hα : S.π α ≠ 0) :
    delta (Fsh5 R m r) α β ≤ 2 * Fintype.card K ∧ (S.π α ≠ 1 → delta (Fsh5 R m r) α β ≤ 2) := by
  haveI := S.charP2
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have hord : S.π α ≠ 1 → delta (Fsh5 R m r) α β ≤ 2 := by
    intro h1
    apply S.ordinary_le hcard
    · intro t ht
      rw [S.fam5_sh_map, p5_deriv_add m r (by omega) (by omega) t (S.π α)] at ht
      have hk : (F5 K m r).derivative.eval (S.π α) = (F5 K m r).derivative.eval 0 := by
        linear_combination ht
      rcases (p5_ker m r hm5 hr5 hrm hm hcop _).mp hk with h | h
      · exact hα h
      · exact h1 h
    · rw [S.fam5_sh_map]; exact hAPN _ hα _
  refine ⟨?_, hord⟩
  by_cases h1 : S.π α = 1
  · exact S.fam5_upper hcard m r hm5 hr5 hrm hodd hmodd hm hcop α β h1
  · exact (hord h1).trans (by omega)

/-- **C2 (valuation preservation), unit differences**: a residue permutation maps unit differences
to unit differences. -/
theorem unit_diff (f : R[X]) (hinj : Function.Injective (fun t : K => (f.map S.π).eval t))
    (x α : R) (hα : S.π α ≠ 0) : S.π (f.eval (x + α) - f.eval x) ≠ 0 := by
  rw [map_sub, S.pi_eval, S.pi_eval, map_add]
  intro h
  exact hα (by have := hinj (sub_eq_zero.mp h); simpa using this)

/-- **C2, non-unit differences**: if p' has no zero, F(x+α) − F(x) = α·y with y a unit mod 2
(so the 2-adic valuation of the difference equals that of α). -/
theorem nonunit_diff (f : R[X]) (hp' : ∀ t : K, (f.map S.π).derivative.eval t ≠ 0)
    (x α : R) (hα : S.π α = 0) : ∃ y, f.eval (x + α) - f.eval x = α * y ∧ S.π y ≠ 0 := by
  obtain ⟨Q, hQ⟩ := taylor2 f x α
  refine ⟨f.derivative.eval x + α * Q, by rw [hQ]; ring, ?_⟩
  rw [map_add, map_mul, hα, zero_mul, add_zero, S.pi_deriv_eval]
  exact hp' _

end GRS

end APN2
