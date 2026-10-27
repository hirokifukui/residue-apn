import Apn2R03.Spectrum3

/-!
# k = 3, μ ≠ 0, arbitrary A: the full exceptional spectrum (S1) (Claude, 2026-10-25)

With s = #A⁻¹(0), z₀ = #(Z ∩ A⁻¹(0)), ν = #{a ∈ Z : A(a) ≠ 0, E(a) ∈ Im L_a}:
  n_q = (s − z₀)·q,   2·n_{2q} = (z₀ + ((q − s) − ν))·q,   4·n_{4q} = ν·q,
and every entry is 0, q, 2q or 4q.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

set_option maxHeartbeats 1000000 in
theorem spectrum_k3 (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ)
    (hm : Fintype.card K = 2 ^ m) (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0)
    (α : R) (hα : S.π α = ρ) :
    let q := Fintype.card K
    let s := (univ.filter (fun a : K => S.Afun f ρ a = 0)).card
    let z0 := (univ.filter (fun a : K => S.Afun f ρ a = 0 ∧ S.Lam f ρ a = 0)).card
    let ν := (univ.filter (fun a : K => S.Afun f ρ a ≠ 0 ∧ (S.Lam f ρ a = 0 ∧
      S.Efun f ρ a ∈ APN2R03.qimg μ (S.Afun f ρ a)))).card
    (univ.filter (fun β : R => delta f α β = q)).card = (s - z0) * q ∧
    2 * (univ.filter (fun β : R => delta f α β = 2 * q)).card = (z0 + ((q - s) - ν)) * q ∧
    4 * (univ.filter (fun β : R => delta f α β = 4 * q)).card = ν * q ∧
    ∀ β, delta f α β = 0 ∨ delta f α β = q ∨ delta f α β = 2 * q ∨ delta f α β = 4 * q := by
  classical
  intro q s z0 ν
  haveI := S.charP2
  have hq : 0 < q := Fintype.card_pos
  have hQ : Fintype.card K ^ (S.k - 1) = q * q := by rw [hk3]; ring
  set T1 := univ.filter (fun a : K => S.Afun f ρ a = 0) with hT1
  set T2 := univ.filter (fun a : K => S.Afun f ρ a ≠ 0) with hT2
  have hT1p : ∀ a ∈ T1, a + ρ ∈ T1 := by
    intro a ha; simp only [T1, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [S.A_periodic f ρ H.hper]; exact ha
  have hT2p : ∀ a ∈ T2, a + ρ ∈ T2 := by
    intro a ha; simp only [T2, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [S.A_periodic f ρ H.hper]; exact ha
  have mem1 : ∀ a, a ∈ T1 ↔ S.Afun f ρ a = 0 := by intro a; simp [T1]
  have mem2 : ∀ a, a ∈ T2 ↔ S.Afun f ρ a ≠ 0 := by intro a; simp [T2]
  -- class data on T1
  have v1 : ∀ a ∈ T1, ∀ β, (S.cc f α β a = 0 ∨ S.cc f α β a = q) ∧
      (S.cc f α β a ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a) = 4 * c) := by
    intro a ha β
    have := S.cc_val_A0_k3 hk3 hcard f ρ μ H hμ0 α β (S.L a) hα (by rw [S.pi_L]; exact (mem1 a).mp ha)
    rwa [S.pi_L] at this
  have v1' : ∀ a ∈ T1, ∀ β, S.cc f α β (a + ρ) ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a + α) = 4 * c := by
    intro a ha β
    have := (S.cc_val_A0_k3 hk3 hcard f ρ μ H hμ0 α β (S.L a + α) hα
      (by rw [S.piL_add α ρ hα, S.A_periodic f ρ H.hper]; exact (mem1 a).mp ha)).2
    rwa [S.piL_add α ρ hα] at this
  -- class data on T2
  have v2 : ∀ a ∈ T2, ∀ β, S.cc f α β a = 0 ∨ S.cc f α β a = 2 * q := by
    intro a ha β
    have := S.cc_val_A hcard f ρ μ H hμ0 α β (S.L a) hα (by rw [S.pi_L]; exact (mem2 a).mp ha)
    rwa [S.pi_L] at this
  have c2 : ∀ a ∈ T2, ∀ β, S.cc f α β a ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a) = 4 * c ∧
      S.π c ∈ APN2R03.qimg μ (S.Afun f ρ a) := by
    intro a ha β
    have := S.cc_ne_zero_iff_A hcard f ρ μ H hμ0 α β (S.L a) hα (by rw [S.pi_L]; exact (mem2 a).mp ha)
    rwa [S.pi_L] at this
  have c2' : ∀ a ∈ T2, ∀ β, S.cc f α β (a + ρ) ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a + α) = 4 * c ∧
      S.π c ∈ APN2R03.qimg μ (S.Afun f ρ a) := by
    intro a ha β
    have := S.cc_ne_zero_iff_A hcard f ρ μ H hμ0 α β (S.L a + α) hα
      (by rw [S.piL_add α ρ hα, S.A_periodic f ρ H.hper]; exact (mem2 a).mp ha)
    rwa [S.piL_add α ρ hα, S.A_periodic f ρ H.hper] at this
  set U1 := T1.filter (fun a => S.Lam f ρ a = 0)
  set U2 := T2.filter (fun a => S.Lam f ρ a = 0 ∧ S.Efun f ρ a ∈ APN2R03.qimg μ (S.Afun f ρ a))
  have h2F := S.two_F
  -- types on T1
  have same1 : ∀ a ∈ U1, ∀ β, S.cc f α β a ≠ 0 ↔ S.cc f α β (a + ρ) ≠ 0 := by
    intro a ha β
    simp only [U1, Finset.mem_filter] at ha
    rw [(v1 a ha.1 β).2, v1' a ha.1]
    exact (S.gate_pair_zero f ρ μ H α β hα a ha.2).1
  have disj1 : ∀ a ∈ T1, a ∉ U1 → ∀ β, ¬ (S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) := by
    intro a ha hU β ⟨h1, h2⟩
    have hL : S.Lam f ρ a ≠ 0 := fun hL => hU (Finset.mem_filter.mpr ⟨ha, hL⟩)
    obtain ⟨c, hc⟩ := (v1 a ha β).2.mp h1
    exact S.gate_exclusive f ρ H.hper α β (S.L a) c hα (by rw [S.pi_L]; exact hL) hc
      ((v1' a ha β).mp h2)
  -- types on T2
  have same2 : ∀ a ∈ U2, ∀ β, S.cc f α β a ≠ 0 ↔ S.cc f α β (a + ρ) ≠ 0 := by
    intro a ha β
    simp only [U2, Finset.mem_filter] at ha
    obtain ⟨haT, hL, hE⟩ := ha
    obtain ⟨hg, hrel⟩ := S.gate_pair_zero f ρ μ H α β hα a hL
    rw [c2 a haT, c2' a haT]
    constructor
    · rintro ⟨c, hc, hmem⟩
      obtain ⟨c', hc'⟩ := hg.mp ⟨c, hc⟩
      exact ⟨c', hc', by rw [hrel c c' hc hc']; exact S.qimg_add μ _ _ _ hmem hE⟩
    · rintro ⟨c', hc', hmem⟩
      obtain ⟨c, hc⟩ := hg.mpr ⟨c', hc'⟩
      refine ⟨c, hc, ?_⟩
      have := S.qimg_add μ _ _ _ hmem hE
      rw [hrel c c' hc hc'] at this
      have e : S.π c + S.Efun f ρ a + S.Efun f ρ a = S.π c := by
        linear_combination (S.Efun f ρ a) * h2F
      rwa [e] at this
  have disj2 : ∀ a ∈ T2, a ∉ U2 → ∀ β, ¬ (S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) := by
    intro a ha hU β ⟨h1, h2⟩
    obtain ⟨c, hc, hmem⟩ := (c2 a ha β).mp h1
    obtain ⟨c', hc', hmem'⟩ := (c2' a ha β).mp h2
    by_cases hL : S.Lam f ρ a = 0
    · obtain ⟨-, hrel⟩ := S.gate_pair_zero f ρ μ H α β hα a hL
      apply hU
      refine Finset.mem_filter.mpr ⟨ha, hL, ?_⟩
      have := S.qimg_add μ _ _ _ hmem hmem'
      rw [hrel c c' hc hc'] at this
      have e : S.π c + (S.π c + S.Efun f ρ a) = S.Efun f ρ a := by linear_combination (S.π c) * h2F
      rwa [e] at this
    · exact S.gate_exclusive f ρ H.hper α β (S.L a) c hα (by rw [S.pi_L]; exact hL) hc ⟨c', hc'⟩
  obtain ⟨A1, B1⟩ := S.sums_from_types' f ρ μ H α hα T1 U1 hT1p (Finset.filter_subset _ _) q
    (Fintype.card K ^ (S.k - 1)) hq (fun a ha => S.card_B hcard f α a q (fun β => (v1 a ha β).1))
    same1 disj1
  obtain ⟨A2, B2⟩ := S.sums_from_types' f ρ μ H α hα T2 U2 hT2p (Finset.filter_subset _ _) (2 * q)
    (Fintype.card K ^ (S.k - 1)) (by positivity) (fun a ha => S.card_B hcard f α a (2 * q) (v2 a ha))
    same2 disj2
  rw [hQ] at A1 B1 A2 B2
  -- value lemma
  have hval : ∀ β a, S.cc f α β a ≠ 0 →
      (a ∈ T1 ∧ delta f α β = q + S.cc f α β (a + ρ) ∧
        (S.cc f α β (a + ρ) = 0 ∨ S.cc f α β (a + ρ) = q)) ∨
      (a ∈ T2 ∧ delta f α β = 2 * q + S.cc f α β (a + ρ) ∧
        (S.cc f α β (a + ρ) = 0 ∨ S.cc f α β (a + ρ) = 2 * q)) := by
    intro β a ha
    by_cases hA : S.Afun f ρ a = 0
    · left
      have haT := (mem1 a).mpr hA
      exact ⟨haT, S.delta_val f ρ μ H α β hα T1 hT1p q (fun a' ha' => (v1 a' ha' β).1) a haT ha⟩
    · right
      have haT := (mem2 a).mpr hA
      exact ⟨haT, S.delta_val f ρ μ H α β hα T2 hT2p (2 * q) (fun a' ha' => v2 a' ha' β) a haT ha⟩
  have eq1 : univ.filter (fun β : R => delta f α β = q) =
      univ.filter (fun β : R => ∃ a ∈ T1, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0) := by
    ext β; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := S.nontriv_delta f α β (by rw [h]; positivity)
      rcases hval β a ha with ⟨haT, hd, hv⟩ | ⟨haT, hd, hv⟩
      · exact ⟨a, haT, ha, by omega⟩
      · omega
    · rintro ⟨a, haT, h1, h2⟩
      rcases hval β a h1 with ⟨-, hd, -⟩ | ⟨haT2, -, -⟩
      · rw [hd, h2, add_zero]
      · exact absurd ((mem1 a).mp haT) ((mem2 a).mp haT2)
  have eq4 : univ.filter (fun β : R => delta f α β = 4 * q) =
      univ.filter (fun β : R => ∃ a ∈ T2, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) := by
    ext β; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := S.nontriv_delta f α β (by rw [h]; positivity)
      rcases hval β a ha with ⟨haT, hd, hv⟩ | ⟨haT, hd, hv⟩
      · omega
      · exact ⟨a, haT, ha, by omega⟩
    · rintro ⟨a, haT, h1, h2⟩
      rcases hval β a h1 with ⟨haT1, -, -⟩ | ⟨-, hd, hv⟩
      · exact absurd ((mem1 a).mp haT1) ((mem2 a).mp haT)
      · rcases hv with h | h
        · exact absurd h h2
        · rw [hd, h]; ring
  have eq2 : univ.filter (fun β : R => delta f α β = 2 * q) =
      univ.filter (fun β : R => ∃ a ∈ T1, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0) ∪
      univ.filter (fun β : R => ∃ a ∈ T2, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0) := by
    ext β; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := S.nontriv_delta f α β (by rw [h]; positivity)
      rcases hval β a ha with ⟨haT, hd, hv⟩ | ⟨haT, hd, hv⟩
      · left; exact ⟨a, haT, ha, by omega⟩
      · right; exact ⟨a, haT, ha, by omega⟩
    · rintro (⟨a, haT, h1, h2⟩ | ⟨a, haT, h1, h2⟩)
      · rcases hval β a h1 with ⟨-, hd, hv⟩ | ⟨haT2, -, -⟩
        · rcases hv with h | h
          · exact absurd h h2
          · rw [hd, h]; ring
        · exact absurd ((mem1 a).mp haT) ((mem2 a).mp haT2)
      · rcases hval β a h1 with ⟨haT1, -, -⟩ | ⟨-, hd, -⟩
        · exact absurd ((mem1 a).mp haT1) ((mem2 a).mp haT)
        · rw [hd, h2, add_zero]
  have hdisj12 : Disjoint
      (univ.filter (fun β : R => ∃ a ∈ T1, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0))
      (univ.filter (fun β : R => ∃ a ∈ T2, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0)) := by
    rw [Finset.disjoint_filter]
    rintro β - ⟨a1, ha1, h1, -⟩ ⟨a2, ha2, h2, -⟩
    rcases S.supp_pair f ρ μ H α β hα a1 a2 h1 h2 with h | h
    · rw [h] at ha2; exact (mem2 a1).mp ha2 ((mem1 a1).mp ha1)
    · rw [h] at ha2; exact (mem2 _).mp ha2 ((mem1 _).mp (hT1p a1 ha1))
  have hT12 : T1.card + T2.card = q := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset K))
      (fun a : K => S.Afun f ρ a = 0)
    rw [Finset.card_univ] at this
    exact this
  have hU2T2 : U2.card ≤ T2.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hU1T1 : U1.card ≤ T1.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hs : s = T1.card := rfl
  have hz0 : z0 = U1.card := by
    simp only [z0, U1, T1, Finset.filter_filter]
  have hν : ν = U2.card := by
    simp only [ν, U2, T2, Finset.filter_filter]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq1]
    have := B1
    unfold N1 at this
    rw [hs, hz0]
    have e : q * (univ.filter (fun β : R => ∃ a ∈ T1, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0)).card
        = q * ((T1.card - U1.card) * q) := by rw [this]; ring
    exact Nat.eq_of_mul_eq_mul_left hq e
  · rw [eq2, Finset.card_union_of_disjoint hdisj12]
    have a1 := A1; have b2 := B2
    unfold N2 at a1; unfold N1 at b2
    have hqs : q - T1.card = T2.card := by omega
    rw [hz0, hν, hs, hqs]
    set n21 := (univ.filter (fun β : R => ∃ a ∈ T1, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)).card
    set n12 := (univ.filter (fun β : R => ∃ a ∈ T2, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) = 0)).card
    have e : q * (2 * (n21 + n12)) = q * ((U1.card + (T2.card - U2.card)) * q) := by
      calc q * (2 * (n21 + n12)) = q * (2 * n21) + 2 * q * n12 := by ring
        _ = U1.card * (q * q) + (T2.card - U2.card) * (q * q) := by rw [a1, b2]
        _ = q * ((U1.card + (T2.card - U2.card)) * q) := by ring
    exact Nat.eq_of_mul_eq_mul_left hq e
  · rw [eq4, hν]
    have a2 := A2
    unfold N2 at a2
    set n22 := (univ.filter (fun β : R => ∃ a ∈ T2, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + ρ) ≠ 0)).card
    have e : q * (4 * n22) = q * (U2.card * q) := by
      calc q * (4 * n22) = 2 * q * (2 * n22) := by ring
        _ = U2.card * (q * q) := a2
        _ = q * (U2.card * q) := by ring
    exact Nat.eq_of_mul_eq_mul_left hq e
  · intro β
    by_cases h0 : delta f α β = 0
    · exact Or.inl h0
    · obtain ⟨a, ha⟩ := S.nontriv_delta f α β h0
      rcases hval β a ha with ⟨-, hd, hv⟩ | ⟨-, hd, hv⟩
      · rcases hv with h | h
        · right; left; rw [hd, h, add_zero]
        · right; right; left; rw [hd, h]; ring
      · rcases hv with h | h
        · right; right; left; rw [hd, h, add_zero]
        · right; right; right; rw [hd, h]; ring

end GRS

end APN2

#print axioms APN2.GRS.spectrum_k3
