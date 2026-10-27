import Apn2R03.Natural

/-!
# The natural lift of P_{m,r} (r ≥ 5) at k = 3: the full exceptional spectrum (Claude, 2026-10-25, R05b)

Paper Corollary 7.5 (cor:natural), multiplicities included.  For every exceptional α:
* n_{2q} = q(q−2)/2 (stated as 2·n_{2q} = q(q−2));
* r ≡ 1 (mod 4): n_{q²} = 2 and every entry is 0, 2q or q²;
* r ≡ 3 (mod 4): n_{2q²} = 1 and every entry is 0, 2q or 2q².
The pairs {a, a+1} with a ∉ {0,1} have A_F ≠ 0 and contribute entries 2q; the pair {0,1} has A_F = 0 and
its two classes collide exactly when E_F(0) = 0, i.e. r ≡ 3 (mod 4).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- E_F on {0,1} for the natural lift (r = 2s+1) -/
theorem fam5_nat_E01 (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (s : ℕ) (hs : r = 2 * s + 1) (a : K)
    (ha : a = 0 ∨ a = 1) : S.Efun (F5 R m r) 1 a = 1 + (s : K) := by
  haveI := S.charP2
  have h2 : (2 : K) = 0 := two_K
  have H := (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).1
  have hA0 := S.fam5_nat_A0 m r hm5 hr5 hrm hodd hm hcop
  have hE0 := S.fam5_nat_E0 m r hm5 hr5 hrm hodd hm hcop s hs
  rcases ha with rfl | rfl
  · exact hE0
  · have := S.E_transl (F5 R m r) 1 0 H.hper H.hμ 0 (S.fam5_Lam (R := R) m r hm5 hr5 hodd 0)
    rw [zero_add, hA0] at this
    rw [← hE0]
    linear_combination this - (S.Efun (F5 R m r) 1 0) * h2

/-- A_F vanishes exactly on {0,1} -/
theorem fam5_nat_A_iff (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (a : K) :
    S.Afun (F5 R m r) 1 a = 0 ↔ (a = 0 ∨ a = 1) := by
  haveI := S.charP2
  have H := (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).1
  have hA0 := S.fam5_nat_A0 m r hm5 hr5 hrm hodd hm hcop
  constructor
  · intro h
    rw [S.fam5_A m r hm5 hr5 hrm hodd hm hcop] at h
    exact A5n_zero m r hm5 hr5 hmodd hm hcop a h
  · rintro (rfl | rfl)
    · exact hA0
    · have := S.A_periodic (F5 R m r) 1 H.hper 0; rw [zero_add] at this; rw [this, hA0]

/-- **Corollary 7.5 with multiplicities.** -/
theorem fam5_nat_k3_spectrum (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (α : R) (hα : S.π α = 1) :
    2 * (univ.filter (fun β : R => delta (F5 R m r) α β = 2 * Fintype.card K)).card =
        Fintype.card K * (Fintype.card K - 2) ∧
      (r % 4 = 1 → (univ.filter (fun β : R => delta (F5 R m r) α β = Fintype.card K ^ 2)).card = 2 ∧
        ∀ β, delta (F5 R m r) α β = 0 ∨ delta (F5 R m r) α β = 2 * Fintype.card K ∨
          delta (F5 R m r) α β = Fintype.card K ^ 2) ∧
      (r % 4 = 3 → (univ.filter (fun β : R => delta (F5 R m r) α β = 2 * Fintype.card K ^ 2)).card = 1 ∧
        ∀ β, delta (F5 R m r) α β = 0 ∨ delta (F5 R m r) α β = 2 * Fintype.card K ∨
          delta (F5 R m r) α β = 2 * Fintype.card K ^ 2) := by
  classical
  haveI := S.charP2
  have h2 : (2 : K) = 0 := two_K
  set f := F5 R m r with hf
  set q := Fintype.card K with hqdef
  have H : S.Hyp f 1 0 := (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).1
  have hq32 : 32 ≤ q := by
    rw [hm]; calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm5
  have hq0 : 0 < q := by omega
  have hsq : 2 * q < q ^ 2 := by nlinarith
  have hkq : q ^ (S.k - 1) = q ^ 2 := by rw [hk3]
  have hAiff := S.fam5_nat_A_iff m r hm5 hr5 hrm hodd hmodd hm hcop
  have hLam : ∀ a, S.Lam f 1 a = 0 := fun a => S.fam5_Lam (R := R) m r hm5 hr5 hodd a
  have hpiL : ∀ a, S.π (S.L a + α) = a + 1 := fun a => S.piL_add α 1 hα a
  have hne01 : ∀ a : K, a + 1 = 0 ↔ a = 1 := fun a =>
    ⟨fun h => by linear_combination h - h2, fun h => by rw [h]; linear_combination h2⟩
  have hne11 : ∀ a : K, a + 1 = 1 ↔ a = 0 := fun a =>
    ⟨fun h => by linear_combination h, fun h => by rw [h, zero_add]⟩
  obtain ⟨s, hs⟩ : ∃ s, r = 2 * s + 1 := ⟨r / 2, by obtain ⟨t, ht⟩ := hodd; omega⟩
  have hE : ∀ a, (a = 0 ∨ a = 1) → S.Efun f 1 a = 1 + (s : K) :=
    S.fam5_nat_E01 m r hm5 hr5 hrm hodd hm hcop s hs
  -- the two kinds of classes
  set T1 : Finset K := (univ : Finset K) \ {0, 1} with hT1
  set T0 : Finset K := {0, 1} with hT0
  have mem1 : ∀ a, a ∈ T1 ↔ ¬ (a = 0 ∨ a = 1) := by
    intro a; rw [hT1, hT0]; simp
  have mem0 : ∀ a, a ∈ T0 ↔ (a = 0 ∨ a = 1) := by intro a; simp [hT0]
  have card1 : T1.card = q - 2 := by
    rw [hT1, hT0, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Finset.card_pair (zero_ne_one)]
  have clos1 : ∀ a ∈ T1, a + 1 ∈ T1 := by
    intro a ha; rw [mem1] at ha ⊢; rw [hne01, hne11]; tauto
  have clos0 : ∀ a ∈ T0, a + 1 ∈ T0 := by
    intro a ha; rw [mem0] at ha ⊢; rw [hne01, hne11]; tauto
  -- values of classes with A ≠ 0 (mu = 0)
  have v1 : ∀ a, ¬ (a = 0 ∨ a = 1) → ∀ β, (S.cc f α β a = 0 ∨ S.cc f α β a = q) ∧
      (S.cc f α β a ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a) = 4 * c) := by
    intro a ha β
    have := S.cc_val_mu0 hcard f 1 H α β (S.L a) hα (by rw [S.pi_L]; exact fun h => ha ((hAiff a).mp h))
    rwa [S.pi_L] at this
  have v1' : ∀ a, ¬ (a = 0 ∨ a = 1) → ∀ β,
      (S.cc f α β (a + 1) ≠ 0 ↔ ∃ c, (Gpoly f α β).eval (S.L a + α) = 4 * c) := by
    intro a ha β
    have := (S.cc_val_mu0 hcard f 1 H α β (S.L a + α) hα (by
      rw [hpiL, S.A_periodic f 1 H.hper]; exact fun h => ha ((hAiff a).mp h))).2
    rwa [hpiL] at this
  -- values of classes with A = 0 (k = 3, mu = 0)
  have v0 : ∀ a, (a = 0 ∨ a = 1) → ∀ β, S.cc f α β a = 0 ∨ S.cc f α β a = q ^ 2 := by
    intro a ha β
    by_cases hg : ∃ c, (Gpoly f α β).eval (S.L a) = 4 * c
    · obtain ⟨c, hc⟩ := hg
      have := S.cc_A0_mu0_k3 hk3 hcard f 1 H α β (S.L a) c hα (by rw [S.pi_L]; exact (hAiff a).mpr ha) hc
      rw [S.pi_L] at this; rw [this]; split_ifs <;> simp [hqdef]
    · left; have := S.cc_zero f 1 H.hper α β (S.L a) hα hg; rwa [S.pi_L] at this
  -- class a ∈ {0,1} nonzero ⇒ gate at L a with residue-0 constant, and then the partner's constant is E(a)
  have pair0 : ∀ a, (a = 0 ∨ a = 1) → ∀ β, S.cc f α β a ≠ 0 →
      (S.cc f α β (a + 1) ≠ 0 ↔ S.Efun f 1 a = 0) := by
    intro a ha β hne
    have hg : ∃ c, (Gpoly f α β).eval (S.L a) = 4 * c := by
      by_contra hn; apply hne; have := S.cc_zero f 1 H.hper α β (S.L a) hα hn; rwa [S.pi_L] at this
    obtain ⟨c, hc⟩ := hg
    have hcc := S.cc_A0_mu0_k3 hk3 hcard f 1 H α β (S.L a) c hα (by rw [S.pi_L]; exact (hAiff a).mpr ha) hc
    rw [S.pi_L] at hcc
    have hπc : S.π c = 0 := by by_contra hn; rw [if_neg hn] at hcc; exact hne hcc
    obtain ⟨c', hc', hπc'⟩ := S.cc_shift f 1 H.hper α β (S.L a) c hα (by rw [S.pi_L]; exact hLam a) hc
    rw [S.pi_L, hπc, zero_add] at hπc'
    have hA1 : S.Afun f 1 (S.π (S.L a + α)) = 0 := by
      rw [hpiL, S.A_periodic f 1 H.hper]; exact (hAiff a).mpr ha
    have hcc' := S.cc_A0_mu0_k3 hk3 hcard f 1 H α β (S.L a + α) c' hα hA1 hc'
    rw [hpiL, hπc'] at hcc'
    rw [hcc']
    constructor
    · intro h; by_contra hn; rw [if_neg hn] at h; exact h rfl
    · intro h; rw [if_pos h]; positivity
  -- β with an entry: the pair through a class a with cc ≠ 0
  have hT : ∀ a ∈ (univ : Finset K), a + 1 ∈ (univ : Finset K) := fun _ _ => Finset.mem_univ _
  -- Part 1: n_{2q}
  have hsame1 : ∀ a ∈ T1, ∀ β, S.cc f α β a ≠ 0 ↔ S.cc f α β (a + 1) ≠ 0 := by
    intro a ha β
    rw [mem1] at ha
    rw [(v1 a ha β).2, v1' a ha β]
    exact (S.gate_pair_zero f 1 0 H α β hα a (hLam a)).1
  obtain ⟨hN2, -⟩ := S.sums_from_types' f 1 0 H α hα T1 T1 clos1 (subset_refl _) q (q ^ (S.k - 1)) hq0
    (fun a ha => S.card_B hcard f α a q (fun β => (v1 a ((mem1 a).mp ha) β).1)) hsame1
    (fun a ha hna => absurd ha hna)
  rw [card1, hkq] at hN2
  have e2q : univ.filter (fun β : R => delta f α β = 2 * q) =
      univ.filter (fun β : R => ∃ a ∈ T1, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + 1) ≠ 0) := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := S.nontriv_delta f α β (by rw [h]; positivity)
      have hd := S.delta_at f 1 0 H α β hα a ha
      by_cases h01 : a = 0 ∨ a = 1
      · exfalso
        have va := v0 a h01 β
        have vb := v0 (a + 1) ((mem0 _).mp (clos0 a ((mem0 a).mpr h01))) β
        rw [hd] at h
        rcases va with va | va
        · exact ha va
        · rcases vb with vb | vb
          · rw [va, vb] at h; linarith [hsq, hq0]
          · rw [va, vb] at h; linarith [hsq, hq0]
      · refine ⟨a, (mem1 a).mpr h01, ha, (hsame1 a ((mem1 a).mpr h01) β).mp ha⟩
    · rintro ⟨a, ha, h1, h2'⟩
      have hd := S.delta_at f 1 0 H α β hα a h1
      have ha' := (mem1 a).mp ha
      have hb' : ¬ (a + 1 = 0 ∨ a + 1 = 1) := (mem1 _).mp (clos1 a ha)
      rcases (v1 a ha' β).1 with h | h
      · exact absurd h h1
      · rcases (v1 (a + 1) hb' β).1 with h' | h'
        · exact absurd h' h2'
        · rw [hd, h, h']; ring
  -- general shape of an entry
  have shape : ∀ β, delta f α β = 0 ∨ delta f α β = 2 * q ∨
      ∃ a, (a = 0 ∨ a = 1) ∧ S.cc f α β a ≠ 0 ∧ delta f α β = S.cc f α β a + S.cc f α β (a + 1) := by
    intro β
    by_cases h0 : delta f α β = 0
    · exact Or.inl h0
    · obtain ⟨a, ha⟩ := S.nontriv_delta f α β h0
      have hd := S.delta_at f 1 0 H α β hα a ha
      by_cases h01 : a = 0 ∨ a = 1
      · exact Or.inr (Or.inr ⟨a, h01, ha, hd⟩)
      · right; left
        have hb' : ¬ (a + 1 = 0 ∨ a + 1 = 1) := (mem1 _).mp (clos1 a ((mem1 a).mpr h01))
        rcases (v1 a h01 β).1 with h | h
        · exact absurd h ha
        · rcases (v1 (a + 1) hb' β).1 with h' | h'
          · exact absurd h' ((hsame1 a ((mem1 a).mpr h01) β).mp ha)
          · rw [hd, h, h']; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e2q]; unfold N2 at hN2
    have : q * (2 * (univ.filter (fun β : R => ∃ a ∈ T1, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + 1) ≠ 0)).card)
        = q * (q * (q - 2)) := by rw [hN2]; ring
    exact Nat.eq_of_mul_eq_mul_left hq0 this
  · intro hr1
    have hsE : (s : K) = 0 := by rw [CharP.cast_eq_zero_iff K 2]; omega
    have hdisj : ∀ a ∈ T0, a ∉ (∅ : Finset K) → ∀ β, ¬ (S.cc f α β a ≠ 0 ∧ S.cc f α β (a + 1) ≠ 0) := by
      intro a ha _ β ⟨h1, h2'⟩
      have := (pair0 a ((mem0 a).mp ha) β h1).mp h2'
      rw [hE a ((mem0 a).mp ha), hsE, add_zero] at this
      exact one_ne_zero this
    obtain ⟨-, hN1⟩ := S.sums_from_types' f 1 0 H α hα T0 ∅ clos0 (Finset.empty_subset _) (q ^ 2)
      (q ^ (S.k - 1)) (by positivity)
      (fun a ha => S.card_B hcard f α a (q ^ 2) (fun β => v0 a ((mem0 a).mp ha) β))
      (fun a ha => absurd ha (Finset.notMem_empty a)) hdisj
    rw [hkq, Finset.card_empty, Nat.sub_zero, hT0, Finset.card_pair zero_ne_one] at hN1
    have eq2 : univ.filter (fun β : R => delta f α β = q ^ 2) =
        univ.filter (fun β : R => ∃ a ∈ T0, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + 1) = 0) := by
      ext β
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases shape β with h0 | h0 | ⟨a, h01, ha, hd⟩
        · rw [h0] at h; linarith [hsq, hq0]
        · rw [h0] at h; linarith [hsq, hq0]
        · refine ⟨a, (mem0 a).mpr h01, ha, ?_⟩
          by_contra hb
          exact hdisj a ((mem0 a).mpr h01) (Finset.notMem_empty a) β ⟨ha, hb⟩
      · rintro ⟨a, ha, h1, h2'⟩
        have hd := S.delta_at f 1 0 H α β hα a h1
        rcases v0 a ((mem0 a).mp ha) β with h | h
        · exact absurd h h1
        · rw [hd, h, h2', add_zero]
    refine ⟨?_, fun β => ?_⟩
    · rw [eq2]; unfold N1 at hN1
      have : q ^ 2 * (univ.filter (fun β : R => ∃ a ∈ T0, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + 1) = 0)).card
          = q ^ 2 * 2 := by rw [hN1]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    · rcases shape β with h0 | h0 | ⟨a, h01, ha, hd⟩
      · exact Or.inl h0
      · exact Or.inr (Or.inl h0)
      · right; right
        have hb : S.cc f α β (a + 1) = 0 := by
          by_contra hb; exact hdisj a ((mem0 a).mpr h01) (Finset.notMem_empty a) β ⟨ha, hb⟩
        rcases v0 a h01 β with h | h
        · exact absurd h ha
        · rw [hd, h, hb, add_zero]
  · intro hr3
    have hsE : (s : K) = 1 := by
      obtain ⟨t, ht⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      rw [ht]; push_cast; rw [h2]; ring
    have hE0' : ∀ a, (a = 0 ∨ a = 1) → S.Efun f 1 a = 0 := by
      intro a ha; rw [hE a ha, hsE]; linear_combination h2
    have hsame0 : ∀ a ∈ T0, ∀ β, S.cc f α β a ≠ 0 ↔ S.cc f α β (a + 1) ≠ 0 := by
      intro a ha β
      have ha' := (mem0 a).mp ha
      have hb' := (mem0 _).mp (clos0 a ha)
      constructor
      · intro h1; exact (pair0 a ha' β h1).mpr (hE0' a ha')
      · intro h2'
        have := (pair0 (a + 1) hb' β h2').mpr (hE0' _ hb')
        rwa [S.add_rho_rho] at this
    obtain ⟨hN2', -⟩ := S.sums_from_types' f 1 0 H α hα T0 T0 clos0 (subset_refl _) (q ^ 2)
      (q ^ (S.k - 1)) (by positivity)
      (fun a ha => S.card_B hcard f α a (q ^ 2) (fun β => v0 a ((mem0 a).mp ha) β)) hsame0
      (fun a ha hna => absurd ha hna)
    rw [hkq, hT0, Finset.card_pair zero_ne_one] at hN2'
    have eq22 : univ.filter (fun β : R => delta f α β = 2 * q ^ 2) =
        univ.filter (fun β : R => ∃ a ∈ T0, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + 1) ≠ 0) := by
      ext β
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases shape β with h0 | h0 | ⟨a, h01, ha, hd⟩
        · rw [h0] at h; linarith [hsq, hq0]
        · rw [h0] at h; linarith [hsq, hq0]
        · exact ⟨a, (mem0 a).mpr h01, ha, (hsame0 a ((mem0 a).mpr h01) β).mp ha⟩
      · rintro ⟨a, ha, h1, h2'⟩
        have hd := S.delta_at f 1 0 H α β hα a h1
        rcases v0 a ((mem0 a).mp ha) β with h | h
        · exact absurd h h1
        · rcases v0 (a + 1) ((mem0 _).mp (clos0 a ha)) β with h' | h'
          · exact absurd h' h2'
          · rw [hd, h, h']; ring
    refine ⟨?_, fun β => ?_⟩
    · rw [eq22]; unfold N2 at hN2'
      have : q ^ 2 * (2 * (univ.filter (fun β : R => ∃ a ∈ T0, S.cc f α β a ≠ 0 ∧ S.cc f α β (a + 1) ≠ 0)).card)
          = q ^ 2 * (2 * 1) := by rw [hN2']; ring
      have := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q ^ 2) this
      omega
    · rcases shape β with h0 | h0 | ⟨a, h01, ha, hd⟩
      · exact Or.inl h0
      · exact Or.inr (Or.inl h0)
      · right; right
        have hb := (hsame0 a ((mem0 a).mpr h01) β).mp ha
        rcases v0 a h01 β with h | h
        · exact absurd h ha
        · rcases v0 (a + 1) ((mem0 _).mp (clos0 a ((mem0 a).mpr h01))) β with h' | h'
          · exact absurd h' hb
          · rw [hd, h, h']; ring

end GRS

end APN2

#print axioms APN2.GRS.fam5_nat_E01
#print axioms APN2.GRS.fam5_nat_A_iff
#print axioms APN2.GRS.fam5_nat_k3_spectrum
