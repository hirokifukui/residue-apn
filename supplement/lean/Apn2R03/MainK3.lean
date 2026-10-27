import Apn2R03.MainK4

/-!
# k = 3: local count for arbitrary A, minimax and all minimizers (Claude, 2026-10-25)

`vmin3` = q if Λ has no zero, 2q otherwise (k = 3 column of the minimax table).
* `class_count3`   : at k = 3 the class count is q·#roots for any G'(x_a)/2 (no simplicity needed).
* `minimax_k3_lower`, `minimax_k3_attain`.
* `minimizers_k3`  : the three-case classification (μ = 0; μ ≠ 0, Z = ∅; μ ≠ 0, Z ≠ ∅).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem class_count3 (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (G : R[X])
    (xa c g : R) (hc : G.eval xa = 4 * c) (hg : G.derivative.eval xa = 2 * g) :
    (univ.filter (fun x : R => S.π x = S.π xa ∧ G.eval x = 0)).card =
      Fintype.card K * (univ.filter (fun y : K =>
        S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card := by
  obtain ⟨P, hP4, hPbar⟩ := S.exists_local_poly G xa c g hc hg
  have hTcard := S.card_T_one hcard P
  have hroots : univ.filter (fun t : K => (P.map S.π).eval t = 0) =
      univ.filter (fun y : K =>
        S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, (hPbar y).1]
  rw [hroots, show S.k - 1 = 2 by omega] at hTcard
  have hT : ∀ z, z ∈ T P 1 ↔ G.eval (xa + 2 * z) = 0 := by
    intro z
    rw [mem_T, ← hP4, S.four_mul_eq_zero_iff, show S.k - 2 = 1 by omega]
  set C0 := univ.filter (fun x : R => S.π x = S.π xa ∧ G.eval x = 0) with hC0
  have key := Finset.card_eq_sum_card_fiberwise (s := T P 1) (t := C0)
    (f := fun z => xa + 2 * z) (fun z hz => by
      rw [Finset.mem_coe, hC0, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, (hT z).mp hz⟩
      rw [map_add, S.pi_two_mul, add_zero])
  have hfib : ∀ x ∈ C0, ((T P 1).filter (fun z => xa + 2 * z = x)).card = Fintype.card K := by
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
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have : (univ.filter (fun y : K =>
      S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card *
      Fintype.card K ^ 2 = (Fintype.card K * (univ.filter (fun y : K =>
      S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card) * Fintype.card K := by
    ring
  rw [this] at key
  exact (Nat.eq_of_mul_eq_mul_right hq key).symm

theorem cc3_formula (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ) (α β xa c : R) (hα : S.π α = ρ)
    (hc : (Gpoly f α β).eval xa = 4 * c) :
    S.cc f α β (S.π xa) = Fintype.card K *
      (univ.filter (fun y : K => S.π c + S.Afun f ρ (S.π xa) * y + μ * y ^ 2 = 0)).card := by
  obtain ⟨g, hg, hπg⟩ := S.A_spec f ρ H.hper xa α (S.π xa) rfl hα
  have h := S.class_count3 hk3 hcard (Gpoly f α β) xa c g hc (by rw [Gpoly_deriv_eval]; exact hg)
  have hh : S.π ((hasseDeriv 2 (Gpoly f α β)).eval xa) = μ := by
    rw [Gpoly_hasse2_eval, map_sub, S.pi_hasse2_eval, S.pi_hasse2_eval, map_add, hα, H.hμ]
  rw [hh, hπg] at h
  exact h

theorem roots_A0 (S : GRS R K) (μ c : K) (hμ : μ ≠ 0) :
    (univ.filter (fun y : K => c + 0 * y + μ * y ^ 2 = 0)).card = 1 := by
  obtain ⟨t, ht⟩ := S.exists_sqrt (c / μ)
  rw [Finset.card_eq_one]
  refine ⟨t, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, zero_mul, add_zero]
  have h2 := S.two_F
  constructor
  · intro h
    apply S.sq_injective
    simp only
    rw [ht]
    field_simp
    linear_combination h - c * h2
  · intro h
    rw [h, ht]
    field_simp
    linear_combination c * h2

theorem cc3_le (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0) (α β : R) (hα : S.π α = ρ) (x : R) :
    S.cc f α β (S.π x) ≤ Fintype.card K * (if S.Afun f ρ (S.π x) = 0 then 1 else 2) := by
  by_cases hc : ∃ c, (Gpoly f α β).eval x = 4 * c
  · obtain ⟨c, hc⟩ := hc
    rw [S.cc3_formula hk3 hcard f ρ μ H α β x c hα hc]
    apply Nat.mul_le_mul_left
    split_ifs with hA
    · rw [hA, S.roots_A0 μ _ hμ0]
    · exact S.roots_le_two μ _ _ hμ0 hA
  · rw [S.cc_zero f ρ H.hper α β x hα hc]; exact Nat.zero_le _

/-- the k = 3 minimax value -/
noncomputable def vmin3 (f : R[X]) (ρ : K) : ℕ :=
  by classical exact if ∀ a, S.Lam f ρ a ≠ 0 then Fintype.card K else 2 * Fintype.card K

theorem minimax_k3_lower (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ) : ∃ β, S.vmin3 f ρ ≤ delta f α β := by
  unfold vmin3
  split_ifs with hv
  · exact S.lower_q hcard f ρ μ H α hα
  · push Not at hv
    obtain ⟨a, ha⟩ := hv
    exact S.lower_2q hcard f ρ μ H α hα a ha

/-- μ ≠ 0, k = 3: the bound for a lift with arbitrary A, given χ = 1 on the Λ-zero pairs with A ≠ 0 -/
theorem upper_k3_mu (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ)
    (hm : Fintype.card K = 2 ^ m) (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0)
    (hχ : ∀ a, S.Lam f ρ a = 0 → S.Afun f ρ a ≠ 0 → S.Efun f ρ a ∉ APN2R03.qimg μ (S.Afun f ρ a))
    (α β : R) (hα : S.π α = ρ) :
    delta f α β ≤ 2 * Fintype.card K ∧
      ((∀ a, S.Lam f ρ a ≠ 0) → (∀ a, S.Afun f ρ a = 0) → delta f α β ≤ Fintype.card K) := by
  haveI := S.charP2
  rcases S.delta_pair' f ρ μ H α β hα with h | ⟨a0, h⟩
  · rw [h]; exact ⟨Nat.zero_le _, fun _ _ => Nat.zero_le _⟩
  · rw [h]
    set xa := S.L a0
    have hxa : S.π xa = a0 := S.pi_L a0
    have hxb : S.π (xa + α) = a0 + ρ := by rw [map_add, hxa, hα]
    have h1 := S.cc3_le hk3 hcard f ρ μ H hμ0 α β hα xa
    have h2 := S.cc3_le hk3 hcard f ρ μ H hμ0 α β hα (xa + α)
    rw [hxb, S.A_periodic f ρ H.hper] at h2
    rw [hxa] at h1
    rw [hxa, hxb]
    have hq0 : 0 < Fintype.card K := Fintype.card_pos
    by_cases hL : S.Lam f ρ a0 = 0
    · refine ⟨?_, fun hZ _ => absurd hL (hZ a0)⟩
      by_cases hA : S.Afun f ρ a0 = 0
      · simp only [hA, if_true, mul_one] at h1 h2; omega
      · by_cases hc : ∃ c, (Gpoly f α β).eval xa = 4 * c
        · obtain ⟨c, hc⟩ := hc
          obtain ⟨c', hc', hπc'⟩ := S.cc_shift f ρ H.hper α β xa c hα (by rw [hxa]; exact hL) hc
          have hcc1 := S.cc3_formula hk3 hcard f ρ μ H α β xa c hα hc
          have hcc2 := S.cc3_formula hk3 hcard f ρ μ H α β (xa + α) c' hα hc'
          rw [hxa] at hcc1
          rw [hxb, S.A_periodic f ρ H.hper, hπc', hxa] at hcc2
          rw [hcc1, hcc2, S.roots_eq_nfib, S.roots_eq_nfib, ← mul_add]
          have := (APN2R03.local_pair_count m hm μ (S.Afun f ρ a0) (S.Efun f ρ a0) hμ0 hA).2
            (hχ a0 hL hA) (S.π c)
          rw [this]; ring_nf; exact le_refl _
        · have e1 := S.cc_zero f ρ H.hper α β xa hα hc
          have e2 := S.cc_zero f ρ H.hper α β (xa + α) hα (S.gate_same f ρ H.hper α β xa hα
            (by rw [hxa]; exact hL) hc)
          rw [hxa] at e1; rw [hxb] at e2
          rw [e1, e2]; exact Nat.zero_le _
    · by_cases hc : ∃ c, (Gpoly f α β).eval xa = 4 * c
      · obtain ⟨c, hc⟩ := hc
        have e2 := S.cc_zero f ρ H.hper α β (xa + α) hα
          (S.gate_exclusive f ρ H.hper α β xa c hα (by rw [hxa]; exact hL) hc)
        rw [hxb] at e2
        rw [e2]
        refine ⟨by split_ifs at h1 <;> omega, fun _ hA0 => ?_⟩
        simp only [hA0, if_true, mul_one] at h1; omega
      · have e1 := S.cc_zero f ρ H.hper α β xa hα hc
        rw [hxa] at e1
        rw [e1]
        refine ⟨by split_ifs at h2 <;> omega, fun _ hA0 => ?_⟩
        simp only [hA0, if_true, mul_one] at h2; omega

theorem minimax_k3_attain (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ)
    (hm : Fintype.card K = 2 ^ m) (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) :
    ∃ g : R[X], g.map S.π = f.map S.π ∧ ∀ α β, S.π α = ρ → delta g α β ≤ S.vmin3 f ρ := by
  by_cases hμ : μ = 0
  · subst hμ
    obtain ⟨H1, hH1⟩ := S.A_prescribe f ρ H.hρ H.hper (fun _ => 1) (fun _ => rfl)
    set g1 := f + C 2 * H1
    have hg1 : g1.map S.π = f.map S.π := S.map_add_two f H1
    have H1' : S.Hyp g1 ρ 0 := S.hyp_of_map_eq f g1 hg1 ρ 0 H
    have hA1 : ∀ a, S.Afun g1 ρ a ≠ 0 := by intro a; rw [hH1]; exact one_ne_zero
    refine ⟨g1, hg1, fun α β hα => ?_⟩
    unfold vmin3
    split_ifs with hv
    · exact S.upper_mu0_Zempty hcard g1 ρ H1' hA1
        (fun a => by rw [S.Lam_of_map_eq f g1 hg1]; exact hv a) α β hα
    · have := S.upper_basic hcard g1 ρ 0 H1' hA1 α β hα
      simpa using this
  · obtain ⟨H0, hH0⟩ := S.A_prescribe f ρ H.hρ H.hper (fun _ => 0) (fun _ => rfl)
    set g0 := f + C 2 * H0
    have hg0 : g0.map S.π = f.map S.π := S.map_add_two f H0
    have H0' : S.Hyp g0 ρ μ := S.hyp_of_map_eq f g0 hg0 ρ μ H
    refine ⟨g0, hg0, fun α β hα => ?_⟩
    have hb := S.upper_k3_mu hk3 hcard m hm g0 ρ μ H0' hμ
      (fun a _ hA => absurd (hH0 a) hA) α β hα
    unfold vmin3
    split_ifs with hv
    · exact hb.2 (fun a => by rw [S.Lam_of_map_eq f g0 hg0]; exact hv a) hH0
    · exact hb.1

/-- all minimizers at k = 3 -/
theorem minimizers_k3 (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ)
    (hm : Fintype.card K = 2 ^ m) (hq : 2 < Fintype.card K) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) :
    (∀ α β, S.π α = ρ → delta f α β ≤ S.vmin3 f ρ) ↔
      ((μ = 0 → ∀ a, S.Afun f ρ a ≠ 0) ∧
       (μ ≠ 0 → (∀ a, S.Lam f ρ a ≠ 0) → ∀ a, S.Afun f ρ a = 0) ∧
       (μ ≠ 0 → ∀ a, S.Lam f ρ a = 0 → S.Afun f ρ a ≠ 0 →
          S.Efun f ρ a ∉ APN2R03.qimg μ (S.Afun f ρ a))) := by
  have hα0 : S.π (S.L ρ) = ρ := S.pi_L ρ
  have hq0 : 0 < Fintype.card K := Fintype.card_pos
  have hvle : S.vmin3 f ρ ≤ 2 * Fintype.card K := by unfold vmin3; split_ifs <;> omega
  constructor
  · intro hopt
    refine ⟨fun hμ a hA => ?_, fun hμ hZ a => ?_, fun hμ a hL hA hE => ?_⟩
    · -- μ = 0, A(a) = 0: an entry q²
      subst hμ
      set xa := S.L a
      set β := f.eval (xa + S.L ρ) - f.eval xa
      have h0 : (Gpoly f (S.L ρ) β).eval xa = 4 * 0 := by rw [Gpoly_eval]; ring
      have hcc := S.cc3_formula hk3 hcard f ρ 0 H (S.L ρ) β xa 0 hα0 h0
      rw [S.pi_L, hA] at hcc
      have hall : univ.filter (fun y : K => S.π 0 + 0 * y + 0 * y ^ 2 = 0) = univ := by
        ext y; simp
      rw [hall, Finset.card_univ] at hcc
      have := le_trans (le_of_eq hcc.symm) (S.cc_le_delta f (S.L ρ) β a)
      have := hopt (S.L ρ) β hα0
      nlinarith
    · by_contra hA
      obtain ⟨β, hβ⟩ := S.lower_2q_A hcard f ρ μ H hμ (S.L ρ) hα0 a hA
      have := hopt (S.L ρ) β hα0
      unfold vmin3 at this; rw [if_pos hZ] at this
      omega
    · obtain ⟨β, hβ⟩ := S.lower_4q hcard f ρ μ H hμ (S.L ρ) hα0 a hA hL hE
      have := hopt (S.L ρ) β hα0
      omega
  · rintro ⟨h0, hZ, hχ⟩ α β hα
    by_cases hμ : μ = 0
    · have hA := h0 hμ
      subst hμ
      unfold vmin3
      split_ifs with hv
      · exact S.upper_mu0_Zempty hcard f ρ H hA hv α β hα
      · have := S.upper_basic hcard f ρ 0 H hA α β hα
        simpa using this
    · have hb := S.upper_k3_mu hk3 hcard m hm f ρ μ H hμ (hχ hμ) α β hα
      unfold vmin3
      split_ifs with hv
      · exact hb.2 hv (hZ hμ hv)
      · exact hb.1

end GRS

end APN2

#print axioms APN2.GRS.class_count3
#print axioms APN2.GRS.minimax_k3_lower
#print axioms APN2.GRS.minimax_k3_attain
#print axioms APN2.GRS.minimizers_k3
