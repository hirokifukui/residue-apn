import Apn2R03.Control

/-!
# Minimax and all minimizers for k ≥ 4 (Claude, 2026-10-25)

`vmin` = q if μ = 0 and Λ has no zero, 2q otherwise (the k ≥ 4 column of the minimax table).
* `minimax_k4`    : every lift has an exceptional entry ≥ vmin, and some lift with the same residue
                    polynomial has all exceptional entries ≤ vmin.
* `minimizers_k4` : a lift attains vmin iff A has no zero and (μ ≠ 0 ⇒ χ = 1 on Z).
* `chi_iff_qimg`  : E ∉ Im(μy²+Ay) ⟺ Tr(μE/A²) ≠ 0.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- the k ≥ 4 minimax value -/
noncomputable def vmin4 (f : R[X]) (ρ μ : K) : ℕ :=
  by classical exact if μ = 0 ∧ ∀ a, S.Lam f ρ a ≠ 0 then Fintype.card K else 2 * Fintype.card K

theorem Lam_of_map_eq (f g : R[X]) (h : g.map S.π = f.map S.π) (ρ a : K) :
    S.Lam g ρ a = S.Lam f ρ a := by unfold Lam; rw [h]

theorem hyp_of_map_eq (f g : R[X]) (h : g.map S.π = f.map S.π) (ρ μ : K) (H : S.Hyp f ρ μ) :
    S.Hyp g ρ μ := ⟨H.hρ, by rw [h]; exact H.hper, by rw [h]; exact H.hμ, by rw [h]; exact H.hdp⟩

theorem vmin4_of_map_eq (f g : R[X]) (h : g.map S.π = f.map S.π) (ρ μ : K) :
    S.vmin4 g ρ μ = S.vmin4 f ρ μ := by
  unfold vmin4; simp only [S.Lam_of_map_eq f g h]

/-- lower half of the minimax theorem, k ≥ 4 -/
theorem minimax_k4_lower (hcard : Fintype.card R = Fintype.card K ^ S.k) (hk4 : 4 ≤ S.k)
    (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ) :
    ∃ β, S.vmin4 f ρ μ ≤ delta f α β := by
  unfold vmin4
  split_ifs with hv
  · exact S.lower_q hcard f ρ μ H α hα
  · by_cases hμ : μ = 0
    · have : ∃ a, S.Lam f ρ a = 0 := by
        by_contra hc; push Not at hc; exact hv ⟨hμ, hc⟩
      obtain ⟨a, ha⟩ := this
      exact S.lower_2q hcard f ρ μ H α hα a ha
    · exact S.lower_2q_k4 hcard hk4 f ρ μ H hμ α hα

/-- upper half: a lift with the same residue polynomial attains vmin at every exceptional α -/
theorem minimax_k4_attain (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ)
    (hm : Fintype.card K = 2 ^ m) (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) :
    ∃ g : R[X], g.map S.π = f.map S.π ∧
      ∀ α β, S.π α = ρ → delta g α β ≤ S.vmin4 f ρ μ := by
  have h2 := S.two_F
  obtain ⟨H1, hH1⟩ := S.A_prescribe f ρ H.hρ H.hper (fun _ => 1) (fun _ => rfl)
  set g1 := f + C 2 * H1
  have hg1 : g1.map S.π = f.map S.π := S.map_add_two f H1
  have H1' : S.Hyp g1 ρ μ := S.hyp_of_map_eq f g1 hg1 ρ μ H
  have hA1 : ∀ a, S.Afun g1 ρ a ≠ 0 := by intro a; rw [hH1]; exact one_ne_zero
  by_cases hμ : μ = 0
  · subst hμ
    refine ⟨g1, hg1, fun α β hα => ?_⟩
    unfold vmin4
    split_ifs with hv
    · exact S.upper_mu0_Zempty hcard g1 ρ H1' hA1
        (fun a => by rw [S.Lam_of_map_eq f g1 hg1]; exact hv.2 a) α β hα
    · have := S.upper_basic hcard g1 ρ 0 H1' hA1 α β hα
      simpa using this
  · obtain ⟨J, hJA, hJE⟩ := S.E_prescribe m hm g1 ρ μ H1' hμ hA1
    set g2 := g1 + C 2 * J ^ 2
    have hg2 : g2.map S.π = f.map S.π := by rw [S.map_add_two g1 (J ^ 2), hg1]
    have H2' : S.Hyp g2 ρ μ := S.hyp_of_map_eq f g2 hg2 ρ μ H
    have hA2 : ∀ a, S.Afun g2 ρ a ≠ 0 := by intro a; rw [hJA]; exact hA1 a
    refine ⟨g2, hg2, fun α β hα => ?_⟩
    have hle := S.upper_mu_chi1 hcard m hm g2 ρ μ H2' hμ hA2
      (fun a ha => by rw [hJA]; exact hJE a ha) α β hα
    unfold vmin4
    rw [if_neg (fun h => hμ h.1)]
    exact hle

/-- all minimizers, k ≥ 4 -/
theorem minimizers_k4 (hcard : Fintype.card R = Fintype.card K ^ S.k) (hk4 : 4 ≤ S.k) (m : ℕ)
    (hm : Fintype.card K = 2 ^ m) (hq : 2 < Fintype.card K) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) :
    (∀ α β, S.π α = ρ → delta f α β ≤ S.vmin4 f ρ μ) ↔
      ((∀ a, S.Afun f ρ a ≠ 0) ∧
        (μ ≠ 0 → ∀ a, S.Lam f ρ a = 0 → S.Efun f ρ a ∉ APN2R03.qimg μ (S.Afun f ρ a))) := by
  have hα0 : S.π (S.L ρ) = ρ := S.pi_L ρ
  have hvle : S.vmin4 f ρ μ ≤ 2 * Fintype.card K := by
    unfold vmin4; split_ifs <;> omega
  constructor
  · intro hopt
    refine ⟨fun a hA => ?_, fun hμ a hL hE => ?_⟩
    · obtain ⟨β, hβ⟩ := S.lower_q2 hcard hk4 f ρ μ H (S.L ρ) hα0 a hA
      have := hopt (S.L ρ) β hα0
      nlinarith
    · by_cases hA : S.Afun f ρ a = 0
      · obtain ⟨β, hβ⟩ := S.lower_q2 hcard hk4 f ρ μ H (S.L ρ) hα0 a hA
        have := hopt (S.L ρ) β hα0
        nlinarith
      · obtain ⟨β, hβ⟩ := S.lower_4q hcard f ρ μ H hμ (S.L ρ) hα0 a hA hL hE
        have := hopt (S.L ρ) β hα0
        have hq0 : 0 < Fintype.card K := Fintype.card_pos
        omega
  · rintro ⟨hA, hχ⟩ α β hα
    unfold vmin4
    by_cases hμ : μ = 0
    · subst hμ
      split_ifs with hv
      · exact S.upper_mu0_Zempty hcard f ρ H hA hv.2 α β hα
      · have := S.upper_basic hcard f ρ 0 H hA α β hα
        simpa using this
    · rw [if_neg (fun h => hμ h.1)]
      exact S.upper_mu_chi1 hcard m hm f ρ μ H hμ hA (hχ hμ) α β hα

/-- χ = 1 in trace form -/
theorem chi_iff_qimg (S : GRS R K) (m : ℕ) (hm1 : 1 ≤ m) (hm : Fintype.card K = 2 ^ m) (μ A E : K) (hμ : μ ≠ 0)
    (hA : A ≠ 0) : E ∉ APN2R03.qimg μ A ↔ APN2R03.absTr m (μ * E / A ^ 2) ≠ 0 := by
  haveI := S.charP2
  rw [ne_eq, ← APN2R03.chi_criterion m hm1 hm μ A E hμ hA]
  unfold APN2R03.qimg
  simp

end GRS

end APN2

#print axioms APN2.GRS.minimax_k4_lower
#print axioms APN2.GRS.minimax_k4_attain
#print axioms APN2.GRS.minimizers_k4
#print axioms APN2.GRS.chi_iff_qimg
