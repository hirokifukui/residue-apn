import Apn2R03.CrossLevel

/-!
# Coherent families across all levels (Claude, 2026-10-25, R05-09)

`cross_level_exists` treats one fixed pair of levels (k, 3).  The paper's Corollary CL2 quantifies over a
whole compatible family (F_k)_{k ≥ 3}.  Here the family is modelled by a common coefficient ring `Rinf`
(for GR this is ℤ[t]/(f̃), whose reductions give every GR(2^k, m)):

* `Tower`: rings `R j` of level j + 3 (j = 0 is level 3), maps `φ j : Rinf → R j`, and for every
  j a compatibility datum `C j` from level j + 4 down to level 3 with `ψ_j ∘ φ_(j+1) = φ_0`;
  `φ_0` is surjective (every level-3 coefficient has an integer representative).
* `coherent_family`: there is a polynomial F over `Rinf` whose reductions are optimal at level 3 and at
  every level ≥ 4 simultaneously, iff μ = 0 or Λ has a zero.

The quantifier "for all levels" is now inside the formal statement.  The concrete tower
ℤ[t]/(f̃) → GR(2^k, m) is not instantiated here (only pairs of levels are instantiated on GR,
`cross_level_exists_GR`).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

/-- Hyp and Λ only depend on the residue polynomial -/
theorem hyp_transfer {R R' K : Type*} [CommRing R] [CommRing R'] [Field K] (S : GRS R K) (S' : GRS R' K)
    (f : R[X]) (f' : R'[X]) (h : f'.map S'.π = f.map S.π) (ρ μ : K) (H : S.Hyp f ρ μ) :
    S'.Hyp f' ρ μ :=
  ⟨H.hρ, by rw [h]; exact H.hper, by rw [h]; exact H.hμ, by rw [h]; exact H.hdp⟩

theorem Lam_transfer {R R' K : Type*} [CommRing R] [CommRing R'] [Field K] (S : GRS R K) (S' : GRS R' K)
    (f : R[X]) (f' : R'[X]) (h : f'.map S'.π = f.map S.π) (ρ a : K) :
    S'.Lam f' ρ a = S.Lam f ρ a := by
  unfold Lam; rw [h]

/-- a coherent tower of Galois-ring structures over a common coefficient ring -/
structure Tower (R : ℕ → Type*) [∀ j, CommRing (R j)] (K : Type*) [Field K] (Rinf : Type*)
    [CommRing Rinf] where
  S : ∀ j, GRS (R j) K
  hlev : ∀ j, (S j).k = j + 3
  C : ∀ j, Compat (S (j + 1)) (S 0)
  φ : ∀ j, Rinf →+* R j
  hφ : ∀ j, ((C j).ψ).comp (φ (j + 1)) = φ 0
  surj0 : Function.Surjective (φ 0)

variable {R : ℕ → Type*} [∀ j, CommRing (R j)] [∀ j, Fintype (R j)] [∀ j, DecidableEq (R j)]
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {Rinf : Type*} [CommRing Rinf]

theorem Tower.map_down (T : Tower R K Rinf) (j : ℕ) (F : Rinf[X]) :
    (F.map (T.φ (j + 1))).map (T.C j).ψ = F.map (T.φ 0) := by
  rw [Polynomial.map_map, T.hφ]

theorem Tower.res_eq (T : Tower R K Rinf) (j : ℕ) (F : Rinf[X]) :
    (F.map (T.φ (j + 1))).map (T.S (j + 1)).π = (F.map (T.φ 0)).map (T.S 0).π := by
  rw [← (T.C j).map_map, T.map_down]

/-- **Corollary CL2 with the quantifier over all levels.** -/
theorem coherent_family (T : Tower R K Rinf)
    (hcard : ∀ j, Fintype.card (R j) = Fintype.card K ^ (T.S j).k)
    (m : ℕ) (hm : Fintype.card K = 2 ^ m) (hq : 2 < Fintype.card K)
    (F0 : Rinf[X]) (ρ μ : K) (H : (T.S 0).Hyp (F0.map (T.φ 0)) ρ μ) :
    (∃ F : Rinf[X], (F.map (T.φ 0)).map (T.S 0).π = (F0.map (T.φ 0)).map (T.S 0).π ∧
        (∀ α β, (T.S 0).π α = ρ →
          delta (F.map (T.φ 0)) α β ≤ (T.S 0).vmin3 (F.map (T.φ 0)) ρ) ∧
        ∀ j, ∀ α β, (T.S (j + 1)).π α = ρ →
          delta (F.map (T.φ (j + 1))) α β ≤ (T.S (j + 1)).vmin4 (F.map (T.φ (j + 1))) ρ μ) ↔
      (μ = 0 ∨ ∃ a, (T.S 0).Lam (F0.map (T.φ 0)) ρ a = 0) := by
  have hk3 : (T.S 0).k = 3 := T.hlev 0
  have hk4 : ∀ j, 4 ≤ (T.S (j + 1)).k := fun j => by rw [T.hlev]; omega
  constructor
  · rintro ⟨F, hres, h3, hk⟩
    have H1 : (T.S 1).Hyp (F.map (T.φ 1)) ρ μ :=
      hyp_transfer (T.S 0) (T.S 1) _ _ (by rw [T.res_eq 0, hres]) ρ μ H
    have h3' : ∀ α β, (T.S 0).π α = ρ → delta ((F.map (T.φ 1)).map (T.C 0).ψ) α β ≤
        (T.S 0).vmin3 ((F.map (T.φ 1)).map (T.C 0).ψ) ρ := by
      rw [T.map_down 0]; exact h3
    have := (cross_level_exists (T.C 0) hk3 (hk4 0) (hcard 0) (hcard 1) m hm hq (F.map (T.φ 1)) ρ μ H1).mp
      ⟨F.map (T.φ 1), rfl, h3', hk 0⟩
    rcases this with h | ⟨a, ha⟩
    · exact Or.inl h
    · refine Or.inr ⟨a, ?_⟩
      rw [Lam_transfer (T.S 1) (T.S 0) (F.map (T.φ 1)) _ (by rw [← hres, ← T.res_eq 0]) ρ a]
      exact ha
  · intro hcase
    have H1 : (T.S 1).Hyp (F0.map (T.φ 1)) ρ μ :=
      hyp_transfer (T.S 0) (T.S 1) _ _ (T.res_eq 0 F0) ρ μ H
    have hcase1 : μ = 0 ∨ ∃ a, (T.S 1).Lam (F0.map (T.φ 1)) ρ a = 0 := by
      rcases hcase with h | ⟨a, ha⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, by rw [Lam_transfer (T.S 0) (T.S 1) _ _ (T.res_eq 0 F0) ρ a]; exact ha⟩
    obtain ⟨g, hg, hg3, hg4⟩ :=
      (cross_level_exists (T.C 0) hk3 (hk4 0) (hcard 0) (hcard 1) m hm hq (F0.map (T.φ 1)) ρ μ H1).mpr hcase1
    have Hg := (T.S 1).hyp_of_map_eq _ g hg ρ μ H1
    have hAg := ((T.S 1).minimizers_k4 (hcard 1) (hk4 0) m hm hq g ρ μ Hg).mp hg4
    obtain ⟨G, hG⟩ := Polynomial.map_surjective (T.φ 0) T.surj0 (g.map (T.C 0).ψ)
    have hresG : (G.map (T.φ 0)).map (T.S 0).π = (F0.map (T.φ 0)).map (T.S 0).π := by
      rw [hG, (T.C 0).map_map, hg, T.res_eq 0]
    refine ⟨G, hresG, by rw [hG]; exact hg3, fun j => ?_⟩
    have Hj : (T.S (j + 1)).Hyp (G.map (T.φ (j + 1))) ρ μ :=
      hyp_transfer (T.S 0) (T.S (j + 1)) _ _ (by rw [T.res_eq j, hresG]) ρ μ H
    have h8 : ∀ α β, (T.S 0).π α = ρ → delta ((G.map (T.φ (j + 1))).map (T.C j).ψ) α β ≤
        (T.S 0).vmin3 ((G.map (T.φ (j + 1))).map (T.C j).ψ) ρ := by
      rw [T.map_down j, hG]; exact hg3
    apply (cross_level_stay (T.C j) hk3 (hk4 j) (hcard 0) (hcard (j + 1)) m hm hq
      (G.map (T.φ (j + 1))) ρ μ Hj h8).mpr
    intro a
    rw [← A_compat (T.C j) _ ρ Hj.hper a, T.map_down j, hG, A_compat (T.C 0) g ρ Hg.hper a]
    exact hAg.1 a

end GRS

end APN2

#print axioms APN2.GRS.coherent_family
