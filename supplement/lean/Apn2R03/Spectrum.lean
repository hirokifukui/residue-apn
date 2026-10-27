import Apn2R03.Layers

/-!
# Full exceptional spectra by double counting (Claude, 2026-10-25)

For an exceptional α, `cc a β` is the contribution of class a to δ(α, β), `Bset a` its support.
* `sum_cc` : Σ_β cc(a, β) = q^(k-1).
* `double2`, `double1` : Σ over a ∈ T of (both classes / only this class) supports = 2·N2(T), N1(T).
* `spectrum_mu` (A nowhere zero, μ ≠ 0, all k ≥ 3):
    2·#{β : δ = 4q} = ν · b,   #{β : δ = 2q} = (q − ν) · b,  with 2q·b = q^(k-1).
* `spectrum_mu0` (A nowhere zero, μ = 0): 2·#{δ = 2q} = z · b, #{δ = q} = (q − z) · b, q·b = q^(k-1).
* `spectrum_k3` (k = 3, μ ≠ 0, arbitrary A): n_q = (s − z₀) q, 2 n_{2q} = (q − s + z₀ − ν) q, 4 n_{4q} = ν q.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem sum_cc (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (α : R) (a : K) :
    ∑ β : R, S.cc f α β a = Fintype.card K ^ (S.k - 1) := by
  rw [← S.card_fiber hcard a]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => f.eval (x + α) - f.eval x)
    (t := (univ : Finset R)) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  apply Finset.sum_congr rfl
  intro β _
  unfold cc
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Gpoly_eval]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linear_combination h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; ring⟩

/-- support of class a in the row of α -/
noncomputable def Bset (f : R[X]) (α : R) (a : K) : Finset R :=
  univ.filter (fun β : R => S.cc f α β a ≠ 0)

theorem card_B (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (α : R) (a : K) (w : ℕ)
    (hval : ∀ β, S.cc f α β a = 0 ∨ S.cc f α β a = w) :
    w * (S.Bset f α a).card = Fintype.card K ^ (S.k - 1) := by
  rw [← S.sum_cc hcard f α a]
  unfold Bset
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rcases hval β with h | h
  · simp [h]
  · by_cases hw : w = 0
    · simp [h, hw]
    · rw [if_pos (by rw [h]; exact hw), h, mul_one]

theorem supp_pair (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α β : R) (hα : S.π α = ρ) (a b : K)
    (ha : S.cc f α β a ≠ 0) (hb : S.cc f α β b ≠ 0) : b = a ∨ b = a + ρ := by
  have ga := S.cc_gate f α β a ha
  have gb := S.cc_gate f α β b hb
  rw [hα] at ga gb
  exact (H.hdp a b).mp (by rw [ga, gb])

theorem add_rho_rho (S : GRS R K) (ρ a : K) : a + ρ + ρ = a := by
  have h2 := S.two_F; linear_combination ρ * h2

noncomputable def N2 (f : R[X]) (α : R) (ρ : K) (T : Finset K) : ℕ :=
  (univ.filter (fun β : R => ∃ a ∈ T, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)).card

noncomputable def N1 (f : R[X]) (α : R) (ρ : K) (T : Finset K) : ℕ :=
  (univ.filter (fun β : R => ∃ a ∈ T, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0)).card

theorem sum_swap (T : Finset K) (P : K → R → Prop) [∀ a β, Decidable (P a β)] :
    ∑ a ∈ T, (univ.filter (fun β : R => P a β)).card =
      ∑ β : R, (T.filter (fun a => P a β)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem double2 (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ) (T : Finset K)
    (hT : ∀ a ∈ T, a + ρ ∈ T) :
    ∑ a ∈ T, (univ.filter (fun β : R => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)).card =
      2 * S.N2 f α ρ T := by
  classical
  rw [sum_swap T (fun a β => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)]
  unfold N2
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs with hex
  · obtain ⟨a0, ha0T, h1, h2⟩ := hex
    have hne : a0 ≠ a0 + ρ := by intro h; apply H.hρ; linear_combination -h
    have : T.filter (fun a => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) = {a0, a0 + ρ} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, ha, -⟩
        exact S.supp_pair f ρ μ H α β hα a0 a h1 ha
      · rintro (rfl | rfl)
        · exact ⟨ha0T, h1, h2⟩
        · exact ⟨hT _ ha0T, h2, by rw [S.add_rho_rho]; exact h1⟩
    rw [this, Finset.card_pair hne]; ring
  · rw [mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha hP
    exact hex ⟨a, ha, hP⟩

theorem double1 (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ) (T : Finset K) :
    ∑ a ∈ T, (univ.filter (fun β : R => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0)).card =
      S.N1 f α ρ T := by
  classical
  rw [sum_swap T (fun a β => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0)]
  unfold N1
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs with hex
  · obtain ⟨a0, ha0T, h1, h2⟩ := hex
    have : T.filter (fun a => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0) = {a0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, ha, -⟩
        rcases S.supp_pair f ρ μ H α β hα a0 a h1 ha with h | h
        · exact h
        · rw [h] at ha; exact absurd h2 ha
      · rintro rfl; exact ⟨ha0T, h1, h2⟩
    rw [this, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha hP
    exact hex ⟨a, ha, hP⟩

theorem sums_from_types (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ)
    (T U : Finset K) (hT : ∀ a ∈ T, a + ρ ∈ T) (hU : U ⊆ T) (b : ℕ)
    (hb : ∀ a ∈ T, (S.Bset f α a).card = b)
    (hsame : ∀ a ∈ U, ∀ β, S.cc f α β a ≠ 0 ↔ S.cc f α β (a + ρ) ≠ 0)
    (hdisj : ∀ a ∈ T, a ∉ U → ∀ β, ¬ (S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)) :
    2 * S.N2 f α ρ T = U.card * b ∧ S.N1 f α ρ T = (T.card - U.card) * b := by
  classical
  have hsplit : ∀ (g : K → ℕ), ∑ a ∈ T, g a = ∑ a ∈ U, g a + ∑ a ∈ T \ U, g a := by
    intro g
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hU]
  constructor
  · rw [← S.double2 f ρ μ H α hα T hT, hsplit]
    have h1 : ∑ a ∈ U, (univ.filter (fun β : R => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)).card
        = U.card * b := by
      rw [Finset.card_eq_sum_ones U, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [one_mul, ← hb a (hU ha)]
      unfold Bset
      congr 1; ext β; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.1, fun h => ⟨h, (hsame a ha β).mp h⟩⟩
    have h2 : ∑ a ∈ T \ U, (univ.filter (fun β : R => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)).card
        = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_sdiff] at ha
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro β _ hP
      exact hdisj a ha.1 ha.2 β hP
    rw [h1, h2, add_zero]
  · rw [← S.double1 f ρ μ H α hα T, hsplit]
    have h1 : ∑ a ∈ U, (univ.filter (fun β : R => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0)).card
        = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro β _ hP
      exact ((hsame a ha β).mp hP.1) hP.2
    have h2 : ∑ a ∈ T \ U, (univ.filter (fun β : R => S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0)).card
        = (T.card - U.card) * b := by
      rw [show T.card - U.card = (T \ U).card by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hU],
        Finset.card_eq_sum_ones (T \ U), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mem_sdiff] at ha
      rw [one_mul, ← hb a ha.1]
      unfold Bset
      congr 1; ext β; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        by_contra h'
        exact hdisj a ha.1 ha.2 β ⟨h, h'⟩
    rw [h1, h2, zero_add]

end GRS

end APN2
