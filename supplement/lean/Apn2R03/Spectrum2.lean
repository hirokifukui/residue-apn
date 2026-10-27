import Apn2R03.Spectrum

/-!
# The three spectrum theorems (Claude, 2026-10-25)

* `spectrum_mu`  (k ≥ 3, A nowhere zero, μ ≠ 0):
    n_{4q}·2 = ν·b, n_{2q} = (q − ν)·b, 2q·b = q^(k-1), all other positive values absent.
* `spectrum_mu0` (k ≥ 3, A nowhere zero, μ = 0):
    n_{2q}·2 = z·b, n_q = (q − z)·b, q·b = q^(k-1).
* `spectrum_k3`  (k = 3, μ ≠ 0, arbitrary A):
    n_q = (s − z₀)·q, 2·n_{2q} = (q − s + z₀ − ν)·q, 4·n_{4q} = ν·q.
Here n_c = #{β : δ(α, β) = c}, ν = #{a : Λ(a) = 0, A(a) ≠ 0, E(a) ∈ Im L_a}, z = #Z, s = #A⁻¹(0), z₀ = #(Z ∩ A⁻¹(0)).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem delta_eq_zero_of (f : R[X]) (α β : R) (h : ∀ a : K, S.cc f α β a = 0) : delta f α β = 0 := by
  rw [S.delta_eq_sum]; exact Finset.sum_eq_zero (fun a _ => h a)

theorem delta_at (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α β : R) (hα : S.π α = ρ) (a : K)
    (ha : S.cc f α β a ≠ 0) : delta f α β = S.cc f α β a + S.cc f α β (a + ρ) := by
  have g := S.cc_gate f α β a ha
  rw [hα] at g
  exact S.delta_pair f α β ρ hα H.hρ H.hdp a g

/-- class a with A(a) ≠ 0, μ ≠ 0: cc ≠ 0 iff the gate passes with constant in Im L -/
theorem cc_ne_zero_iff_A (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0) (α β x : R) (hα : S.π α = ρ) (hA : S.Afun f ρ (S.π x) ≠ 0) :
    S.cc f α β (S.π x) ≠ 0 ↔ ∃ c, (Gpoly f α β).eval x = 4 * c ∧
      S.π c ∈ APN2R03.qimg μ (S.Afun f ρ (S.π x)) := by
  haveI := S.charP2
  have hq : 0 < Fintype.card K := Fintype.card_pos
  constructor
  · intro h
    by_cases hc : ∃ c, (Gpoly f α β).eval x = 4 * c
    · obtain ⟨c, hc⟩ := hc
      refine ⟨c, hc, ?_⟩
      rw [S.cc_formula hcard f ρ μ H.hper H.hμ α β x c hα hc hA, S.roots_eq_nfib,
        APN2R03.nfib_eq μ _ _ hμ0 hA] at h
      by_contra hn; rw [if_neg hn, mul_zero] at h; exact h rfl
    · exact absurd (S.cc_zero f ρ H.hper α β x hα hc) h
  · rintro ⟨c, hc, hmem⟩
    rw [S.cc_formula hcard f ρ μ H.hper H.hμ α β x c hα hc hA, S.roots_eq_nfib,
      APN2R03.nfib_eq μ _ _ hμ0 hA, if_pos hmem]
    omega

theorem cc_val_A (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0) (α β x : R) (hα : S.π α = ρ) (hA : S.Afun f ρ (S.π x) ≠ 0) :
    S.cc f α β (S.π x) = 0 ∨ S.cc f α β (S.π x) = 2 * Fintype.card K := by
  haveI := S.charP2
  by_cases hc : ∃ c, (Gpoly f α β).eval x = 4 * c
  · obtain ⟨c, hc⟩ := hc
    rw [S.cc_formula hcard f ρ μ H.hper H.hμ α β x c hα hc hA, S.roots_eq_nfib,
      APN2R03.nfib_eq μ _ _ hμ0 hA]
    split_ifs
    · right; ring
    · left; ring
  · left; exact S.cc_zero f ρ H.hper α β x hα hc

/-- class a with μ = 0, A(a) ≠ 0: cc ∈ {0, q} and ≠ 0 iff the gate passes -/
theorem cc_val_mu0 (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ : K)
    (H : S.Hyp f ρ 0) (α β x : R) (hα : S.π α = ρ) (hA : S.Afun f ρ (S.π x) ≠ 0) :
    (S.cc f α β (S.π x) = 0 ∨ S.cc f α β (S.π x) = Fintype.card K) ∧
      (S.cc f α β (S.π x) ≠ 0 ↔ ∃ c, (Gpoly f α β).eval x = 4 * c) := by
  have hq : 0 < Fintype.card K := Fintype.card_pos
  by_cases hc : ∃ c, (Gpoly f α β).eval x = 4 * c
  · obtain ⟨c, hc'⟩ := hc
    rw [S.cc_formula hcard f ρ 0 H.hper H.hμ α β x c hα hc' hA, roots_lin _ _ hA]
    exact ⟨Or.inr (by ring), ⟨fun _ => ⟨c, hc'⟩, fun _ => by omega⟩⟩
  · rw [S.cc_zero f ρ H.hper α β x hα hc]
    exact ⟨Or.inl rfl, ⟨fun h => absurd rfl h, fun h => absurd h hc⟩⟩

/-- class a with A(a) = 0 at k = 3, μ ≠ 0: cc ∈ {0, q} and ≠ 0 iff the gate passes -/
theorem cc_val_A0_k3 (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0) (α β x : R) (hα : S.π α = ρ)
    (hA : S.Afun f ρ (S.π x) = 0) :
    (S.cc f α β (S.π x) = 0 ∨ S.cc f α β (S.π x) = Fintype.card K) ∧
      (S.cc f α β (S.π x) ≠ 0 ↔ ∃ c, (Gpoly f α β).eval x = 4 * c) := by
  have hq : 0 < Fintype.card K := Fintype.card_pos
  by_cases hc : ∃ c, (Gpoly f α β).eval x = 4 * c
  · obtain ⟨c, hc'⟩ := hc
    rw [S.cc3_formula hk3 hcard f ρ μ H α β x c hα hc', hA, S.roots_A0 μ _ hμ0]
    exact ⟨Or.inr (by ring), ⟨fun _ => ⟨c, hc'⟩, fun _ => by omega⟩⟩
  · rw [S.cc_zero f ρ H.hper α β x hα hc]
    exact ⟨Or.inl rfl, ⟨fun h => absurd rfl h, fun h => absurd h hc⟩⟩

theorem piL_add (α : R) (ρ : K) (hα : S.π α = ρ) (a : K) : S.π (S.L a + α) = a + ρ := by
  rw [map_add, S.pi_L, hα]

/-- gate transfer across a Λ-zero pair, both directions, with constants related by E -/
theorem gate_pair_zero (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α β : R) (hα : S.π α = ρ) (a : K)
    (hL : S.Lam f ρ a = 0) :
    ((∃ c, (Gpoly f α β).eval (S.L a) = 4 * c) ↔ (∃ c, (Gpoly f α β).eval (S.L a + α) = 4 * c)) ∧
    ∀ c c', (Gpoly f α β).eval (S.L a) = 4 * c → (Gpoly f α β).eval (S.L a + α) = 4 * c' →
      S.π c' = S.π c + S.Efun f ρ a := by
  have hLa : S.Lam f ρ (S.π (S.L a)) = 0 := by rw [S.pi_L]; exact hL
  refine ⟨⟨fun ⟨c, hc⟩ => ?_, fun h => ?_⟩, fun c c' hc hc' => ?_⟩
  · obtain ⟨c', hc', -⟩ := S.cc_shift f ρ H.hper α β (S.L a) c hα hLa hc
    exact ⟨c', hc'⟩
  · by_contra hn
    exact S.gate_same f ρ H.hper α β (S.L a) hα hLa hn h
  · obtain ⟨c'', hc'', hπ⟩ := S.cc_shift f ρ H.hper α β (S.L a) c hα hLa hc
    have : S.π c' = S.π c'' := S.pi_eq_of_four_mul_eq (by rw [← hc', ← hc''])
    rw [this, hπ, S.pi_L]

/-- general value lemma on a periodic set of classes with uniform contribution w -/
theorem delta_val (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α β : R) (hα : S.π α = ρ)
    (T : Finset K) (hT : ∀ a ∈ T, a + ρ ∈ T) (w : ℕ)
    (hval : ∀ a ∈ T, S.cc f α β a = 0 ∨ S.cc f α β a = w) (a : K) (haT : a ∈ T)
    (ha : S.cc f α β a ≠ 0) :
    delta f α β = w + S.cc f α β (a + ρ) ∧ (S.cc f α β (a + ρ) = 0 ∨ S.cc f α β (a + ρ) = w) := by
  have h1 := S.delta_at f ρ μ H α β hα a ha
  rcases hval a haT with h | h
  · exact absurd h ha
  · exact ⟨by rw [h1, h], hval _ (hT a haT)⟩

theorem nontriv_delta (f : R[X]) (α β : R) (h : delta f α β ≠ 0) : ∃ a : K, S.cc f α β a ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (S.delta_eq_zero_of f α β hn)

/-! ## A nowhere zero, μ ≠ 0 -/

theorem spectrum_mu (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ)
    (hm : Fintype.card K = 2 ^ m) (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0)
    (hA : ∀ a, S.Afun f ρ a ≠ 0) (α : R) (hα : S.π α = ρ) :
    ∃ b : ℕ, 2 * Fintype.card K * b = Fintype.card K ^ (S.k - 1) ∧
      2 * (univ.filter (fun β : R => delta f α β = 4 * Fintype.card K)).card =
        (univ.filter (fun a : K => S.Lam f ρ a = 0 ∧
          S.Efun f ρ a ∈ APN2R03.qimg μ (S.Afun f ρ a))).card * b ∧
      (univ.filter (fun β : R => delta f α β = 2 * Fintype.card K)).card =
        (Fintype.card K - (univ.filter (fun a : K => S.Lam f ρ a = 0 ∧
          S.Efun f ρ a ∈ APN2R03.qimg μ (S.Afun f ρ a))).card) * b ∧
      ∀ β, delta f α β = 0 ∨ delta f α β = 2 * Fintype.card K ∨ delta f α β = 4 * Fintype.card K := by
  classical
  haveI := S.charP2
  have hq : 0 < Fintype.card K := Fintype.card_pos
  set w := 2 * Fintype.card K
  have hvalall : ∀ a β, S.cc f α β a = 0 ∨ S.cc f α β a = w := by
    intro a β
    have := S.cc_val_A hcard f ρ μ H hμ0 α β (S.L a) hα (by rw [S.pi_L]; exact hA a)
    rwa [S.pi_L] at this
  have hB : ∀ a, w * (S.Bset f α a).card = Fintype.card K ^ (S.k - 1) :=
    fun a => S.card_B hcard f α a w (fun β => hvalall a β)
  set b := (S.Bset f α 0).card
  have hbconst : ∀ a ∈ (univ : Finset K), (S.Bset f α a).card = b := by
    intro a _
    have h1 := hB a; have h0 := hB 0
    have hw : 0 < w := by positivity
    exact Nat.eq_of_mul_eq_mul_left hw (h1.trans h0.symm)
  set U := univ.filter (fun a : K => S.Lam f ρ a = 0 ∧ S.Efun f ρ a ∈ APN2R03.qimg μ (S.Afun f ρ a))
  -- class criteria via the canonical lifts
  have hcrit : ∀ a β, S.cc f α β a ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a) = 4 * c ∧
      S.π c ∈ APN2R03.qimg μ (S.Afun f ρ a) := by
    intro a β
    have := S.cc_ne_zero_iff_A hcard f ρ μ H hμ0 α β (S.L a) hα (by rw [S.pi_L]; exact hA a)
    rwa [S.pi_L] at this
  have hcrit' : ∀ a β, S.cc f α β (a + ρ) ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a + α) = 4 * c ∧
      S.π c ∈ APN2R03.qimg μ (S.Afun f ρ a) := by
    intro a β
    have := S.cc_ne_zero_iff_A hcard f ρ μ H hμ0 α β (S.L a + α) hα
      (by rw [S.piL_add α ρ hα, S.A_periodic f ρ H.hper]; exact hA a)
    rwa [S.piL_add α ρ hα, S.A_periodic f ρ H.hper] at this
  have hsame : ∀ a ∈ U, ∀ β, S.cc f α β a ≠ 0 ↔ S.cc f α β (a + ρ) ≠ 0 := by
    intro a ha β
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨hL, hE⟩ := ha
    obtain ⟨hg, hrel⟩ := S.gate_pair_zero f ρ μ H α β hα a hL
    rw [hcrit, hcrit']
    constructor
    · rintro ⟨c, hc, hmem⟩
      obtain ⟨c', hc'⟩ := hg.mp ⟨c, hc⟩
      exact ⟨c', hc', by rw [hrel c c' hc hc']; exact S.qimg_add μ _ _ _ hmem hE⟩
    · rintro ⟨c', hc', hmem⟩
      obtain ⟨c, hc⟩ := hg.mpr ⟨c', hc'⟩
      refine ⟨c, hc, ?_⟩
      have := S.qimg_add μ _ _ _ hmem hE
      rw [hrel c c' hc hc'] at this
      have h2 := S.two_F
      have e : S.π c + S.Efun f ρ a + S.Efun f ρ a = S.π c := by linear_combination (S.Efun f ρ a) * h2
      rwa [e] at this
  have hdisj : ∀ a ∈ (univ : Finset K), a ∉ U → ∀ β,
      ¬ (S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) := by
    intro a _ ha β ⟨h1, h2⟩
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at ha
    obtain ⟨c, hc, hmem⟩ := (hcrit a β).mp h1
    obtain ⟨c', hc', hmem'⟩ := (hcrit' a β).mp h2
    by_cases hL : S.Lam f ρ a = 0
    · obtain ⟨-, hrel⟩ := S.gate_pair_zero f ρ μ H α β hα a hL
      apply ha hL
      have := S.qimg_add μ _ _ _ hmem hmem'
      rw [hrel c c' hc hc'] at this
      have h2 := S.two_F
      have e : S.π c + (S.π c + S.Efun f ρ a) = S.Efun f ρ a := by linear_combination (S.π c) * h2
      rwa [e] at this
    · exact S.gate_exclusive f ρ H.hper α β (S.L a) c hα (by rw [S.pi_L]; exact hL) hc ⟨c', hc'⟩
  obtain ⟨hN2, hN1⟩ := S.sums_from_types f ρ μ H α hα univ U (fun _ _ => Finset.mem_univ _)
    (Finset.subset_univ _) b hbconst hsame hdisj
  rw [Finset.card_univ] at hN1
  -- identify the level sets with N2, N1
  have hT : ∀ a ∈ (univ : Finset K), a + ρ ∈ (univ : Finset K) := fun _ _ => Finset.mem_univ _
  have hv : ∀ β, ∀ a ∈ (univ : Finset K), S.cc f α β a = 0 ∨ S.cc f α β a = w :=
    fun β a _ => hvalall a β
  have hw0 : 0 < w := by positivity
  have e4 : univ.filter (fun β : R => delta f α β = 4 * Fintype.card K) =
      univ.filter (fun β : R => ∃ a ∈ (univ : Finset K), S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := S.nontriv_delta f α β (by rw [h]; positivity)
      obtain ⟨hd, hv2⟩ := S.delta_val f ρ μ H α β hα univ hT w (hv β) a (Finset.mem_univ _) ha
      refine ⟨a, ha, ?_⟩
      intro h0; rw [h0] at hd; omega
    · rintro ⟨a, h1, h2⟩
      obtain ⟨hd, hv2⟩ := S.delta_val f ρ μ H α β hα univ hT w (hv β) a (Finset.mem_univ _) h1
      rcases hv2 with h | h
      · exact absurd h h2
      · rw [hd, h]; ring
  have e2 : univ.filter (fun β : R => delta f α β = 2 * Fintype.card K) =
      univ.filter (fun β : R => ∃ a ∈ (univ : Finset K), S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0) := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := S.nontriv_delta f α β (by rw [h]; positivity)
      obtain ⟨hd, hv2⟩ := S.delta_val f ρ μ H α β hα univ hT w (hv β) a (Finset.mem_univ _) ha
      refine ⟨a, ha, ?_⟩
      rcases hv2 with h' | h'
      · exact h'
      · rw [hd, h'] at h; omega
    · rintro ⟨a, h1, h2⟩
      obtain ⟨hd, -⟩ := S.delta_val f ρ μ H α β hα univ hT w (hv β) a (Finset.mem_univ _) h1
      rw [hd, h2]; ring
  refine ⟨b, hbconst 0 (Finset.mem_univ _) ▸ hB 0, ?_, ?_, ?_⟩
  · rw [e4]; exact hN2
  · rw [e2]; exact hN1
  · intro β
    by_cases h0 : delta f α β = 0
    · exact Or.inl h0
    · obtain ⟨a, ha⟩ := S.nontriv_delta f α β h0
      obtain ⟨hd, hv2⟩ := S.delta_val f ρ μ H α β hα univ hT w (hv β) a (Finset.mem_univ _) ha
      rcases hv2 with h | h
      · right; left; rw [hd, h, add_zero]
      · right; right; rw [hd, h]; ring

end GRS

end APN2

#print axioms APN2.GRS.spectrum_mu
