import Apn2R03.Spectrum2

/-!
# Spectra: μ = 0 (all k), and k = 3 with arbitrary A (Claude, 2026-10-25)
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- `sums_from_types` with the class size given by w·|B_a| = Q (allowing T = ∅) -/
theorem sums_from_types' (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ)
    (T U : Finset K) (hT : ∀ a ∈ T, a + ρ ∈ T) (hU : U ⊆ T) (w Q : ℕ) (hw : 0 < w)
    (hb : ∀ a ∈ T, w * (S.Bset f α a).card = Q)
    (hsame : ∀ a ∈ U, ∀ β, S.cc f α β a ≠ 0 ↔ S.cc f α β (a + ρ) ≠ 0)
    (hdisj : ∀ a ∈ T, a ∉ U → ∀ β, ¬ (S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)) :
    w * (2 * S.N2 f α ρ T) = U.card * Q ∧ w * S.N1 f α ρ T = (T.card - U.card) * Q := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨a0, ha0⟩
  · subst hTe
    have hUe : U = ∅ := Finset.subset_empty.mp hU
    subst hUe
    have h2 : S.N2 f α ρ ∅ = 0 := by
      unfold N2; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; simp
    have h1 : S.N1 f α ρ ∅ = 0 := by
      unfold N1; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; simp
    simp [h1, h2]
  · set b := (S.Bset f α a0).card
    have hbc : ∀ a ∈ T, (S.Bset f α a).card = b := fun a ha =>
      Nat.eq_of_mul_eq_mul_left hw ((hb a ha).trans (hb a0 ha0).symm)
    obtain ⟨h2, h1⟩ := S.sums_from_types f ρ μ H α hα T U hT hU b hbc hsame hdisj
    rw [h2, h1, ← hb a0 ha0]
    constructor <;> ring

theorem spectrum_mu0 (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ : K)
    (H : S.Hyp f ρ 0) (hA : ∀ a, S.Afun f ρ a ≠ 0) (α : R) (hα : S.π α = ρ) :
    Fintype.card K * (2 * (univ.filter (fun β : R => delta f α β = 2 * Fintype.card K)).card) =
        (univ.filter (fun a : K => S.Lam f ρ a = 0)).card * Fintype.card K ^ (S.k - 1) ∧
      Fintype.card K * (univ.filter (fun β : R => delta f α β = Fintype.card K)).card =
        (Fintype.card K - (univ.filter (fun a : K => S.Lam f ρ a = 0)).card) *
          Fintype.card K ^ (S.k - 1) ∧
      ∀ β, delta f α β = 0 ∨ delta f α β = Fintype.card K ∨ delta f α β = 2 * Fintype.card K := by
  classical
  have hq : 0 < Fintype.card K := Fintype.card_pos
  set w := Fintype.card K
  have hv0 : ∀ a β, (S.cc f α β a = 0 ∨ S.cc f α β a = w) ∧
      (S.cc f α β a ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a) = 4 * c) := by
    intro a β
    have := S.cc_val_mu0 hcard f ρ H α β (S.L a) hα (by rw [S.pi_L]; exact hA a)
    rwa [S.pi_L] at this
  have hv1 : ∀ a β, S.cc f α β (a + ρ) ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a + α) = 4 * c := by
    intro a β
    have := (S.cc_val_mu0 hcard f ρ H α β (S.L a + α) hα
      (by rw [S.piL_add α ρ hα, S.A_periodic f ρ H.hper]; exact hA a)).2
    rwa [S.piL_add α ρ hα] at this
  set U := univ.filter (fun a : K => S.Lam f ρ a = 0)
  have hsame : ∀ a ∈ U, ∀ β, S.cc f α β a ≠ 0 ↔ S.cc f α β (a + ρ) ≠ 0 := by
    intro a ha β
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [(hv0 a β).2, hv1]
    exact (S.gate_pair_zero f ρ 0 H α β hα a ha).1
  have hdisj : ∀ a ∈ (univ : Finset K), a ∉ U → ∀ β,
      ¬ (S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) := by
    intro a _ ha β ⟨h1, h2⟩
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨c, hc⟩ := (hv0 a β).2.mp h1
    exact S.gate_exclusive f ρ H.hper α β (S.L a) c hα (by rw [S.pi_L]; exact ha) hc ((hv1 a β).mp h2)
  obtain ⟨hN2, hN1⟩ := S.sums_from_types' f ρ 0 H α hα univ U (fun _ _ => Finset.mem_univ _)
    (Finset.subset_univ _) w (Fintype.card K ^ (S.k - 1)) hq
    (fun a _ => S.card_B hcard f α a w (fun β => (hv0 a β).1)) hsame hdisj
  rw [Finset.card_univ] at hN1
  have hT : ∀ a ∈ (univ : Finset K), a + ρ ∈ (univ : Finset K) := fun _ _ => Finset.mem_univ _
  have hv : ∀ β, ∀ a ∈ (univ : Finset K), S.cc f α β a = 0 ∨ S.cc f α β a = w :=
    fun β a _ => (hv0 a β).1
  have e2 : univ.filter (fun β : R => delta f α β = 2 * w) =
      univ.filter (fun β : R => ∃ a ∈ (univ : Finset K), S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := S.nontriv_delta f α β (by rw [h]; positivity)
      obtain ⟨hd, -⟩ := S.delta_val f ρ 0 H α β hα univ hT w (hv β) a (Finset.mem_univ _) ha
      exact ⟨a, ha, fun h0 => by rw [h0] at hd; omega⟩
    · rintro ⟨a, h1, h2⟩
      obtain ⟨hd, hv2⟩ := S.delta_val f ρ 0 H α β hα univ hT w (hv β) a (Finset.mem_univ _) h1
      rcases hv2 with h | h
      · exact absurd h h2
      · rw [hd, h]; ring
  have e1 : univ.filter (fun β : R => delta f α β = w) =
      univ.filter (fun β : R => ∃ a ∈ (univ : Finset K), S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0) := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := S.nontriv_delta f α β (by rw [h]; positivity)
      obtain ⟨hd, hv2⟩ := S.delta_val f ρ 0 H α β hα univ hT w (hv β) a (Finset.mem_univ _) ha
      refine ⟨a, ha, ?_⟩
      rcases hv2 with h' | h'
      · exact h'
      · rw [hd, h'] at h; omega
    · rintro ⟨a, h1, h2⟩
      obtain ⟨hd, -⟩ := S.delta_val f ρ 0 H α β hα univ hT w (hv β) a (Finset.mem_univ _) h1
      rw [hd, h2, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [e2]; exact hN2
  · rw [e1]; exact hN1
  · intro β
    by_cases h0 : delta f α β = 0
    · exact Or.inl h0
    · obtain ⟨a, ha⟩ := S.nontriv_delta f α β h0
      obtain ⟨hd, hv2⟩ := S.delta_val f ρ 0 H α β hα univ hT w (hv β) a (Finset.mem_univ _) ha
      rcases hv2 with h | h
      · right; left; rw [hd, h, add_zero]
      · right; right; rw [hd, h]; ring

end GRS

end APN2

#print axioms APN2.GRS.spectrum_mu0
