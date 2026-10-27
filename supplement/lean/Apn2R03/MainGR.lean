import Apn2R03.GRInst

/-!
# Theorem A on the concrete Galois rings GR(2^k, m) (Claude, 2026-10-25)

* for every m ≥ 1 and k ≥ 1 there is a monic f ∈ (ℤ/2^k)[X] of degree m with f̄ irreducible
  (via a primitive element of GF(2^m) and a monic lift);
* GR(2^k, m) = (ℤ/2^k)[X]/(f) is finite;
* Theorem A (r = 3 and r ≥ 5) holds on GR(2^k, m) with the reduction map of `grs`.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

theorem exists_irred_bin (m : ℕ) (hm : m ≠ 0) :
    ∃ g : (ZMod 2)[X], g.Monic ∧ Irreducible g ∧ g.natDegree = m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ZMod 2) (GaloisField 2 m)
  have hint : IsIntegral (ZMod 2) α := .of_finite _ _
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top',
    GaloisField.finrank 2 hm]

theorem exists_GR_poly (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : m ≠ 0) :
    ∃ f : (ZMod (2 ^ k))[X], f.Monic ∧ f.natDegree = m ∧ Irreducible (f.map (red k hk)) := by
  obtain ⟨g, hgm, hgi, hgd⟩ := exists_irred_bin m hm
  obtain ⟨f, hfmap, hfdeg, hfm⟩ :=
    lifts_and_degree_eq_and_monic (mem_lifts_of_surjective (red_surj k hk) g) hgm
  exact ⟨f, hfm, (natDegree_eq_of_degree_eq hfdeg).trans hgd, by rw [hfmap]; exact hgi⟩

theorem finite_GR (k : ℕ) (f : (ZMod (2 ^ k))[X]) (hf : f.Monic) : Finite (AdjoinRoot f) := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  haveI := (AdjoinRoot.powerBasis' hf).finite
  exact Module.finite_of_finite (ZMod (2 ^ k))

theorem finite_bar (g : (ZMod 2)[X]) (hg : g.Monic) : Finite (AdjoinRoot g) := by
  haveI := (AdjoinRoot.powerBasis' hg).finite
  exact Module.finite_of_finite (ZMod 2)

section main
variable (k : ℕ) (hk : 3 ≤ k) (f : (ZMod (2 ^ k))[X]) (hf : f.Monic)
variable [Fact (Irreducible (fbar k hk f))]
variable [Fintype (AdjoinRoot f)] [DecidableEq (AdjoinRoot f)]
variable [Fintype (AdjoinRoot (fbar k hk f))] [DecidableEq (AdjoinRoot (fbar k hk f))]

/-- **Theorem A (r = 3) on GR(2^k, m).** -/
theorem thmA3_GR (m : ℕ) (hdeg : f.natDegree = m) (hm5 : 5 ≤ m) (hodd : Odd m)
    (h3 : Nat.Coprime 3 m) :
    (∀ α β, (grs k hk f hf).π α = 1 →
        GRS.delta (Fsh3 (AdjoinRoot f) m) α β ≤ 2 * Fintype.card (AdjoinRoot (fbar k hk f))) ∧
    (∀ g : (AdjoinRoot f)[X], g.map (grs k hk f hf).π = Fnat3 _ m → ∀ α, (grs k hk f hf).π α = 1 →
        ∃ β, 2 * Fintype.card (AdjoinRoot (fbar k hk f)) ≤ GRS.delta g α β) ∧
    (∀ α, (grs k hk f hf).π α = 1 →
        ∃ β, 4 * Fintype.card (AdjoinRoot (fbar k hk f)) ≤ GRS.delta (Fnat3 (AdjoinRoot f) m) α β) := by
  obtain ⟨hc, hK⟩ := grs_card k hk f hf
  rw [hdeg] at hK
  set S := grs k hk f hf
  have hcard : Fintype.card (AdjoinRoot f) = Fintype.card (AdjoinRoot (fbar k hk f)) ^ S.k := hc
  exact ⟨fun α β hα => S.fam3_upper hcard m hm5 hodd hK h3 α β hα,
    fun g hg α hα => S.fam3_lower_all hcard m hm5 hK h3 g hg α hα,
    fun α hα => S.fam3_natural hcard m hm5 hodd hK h3 α hα⟩

/-- **Theorem A (r ≥ 5) on GR(2^k, m).** -/
theorem thmA5_GR (m r : ℕ) (hdeg : f.natDegree = m) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m)
    (hodd : Odd r) (hmodd : Odd m) (hcop : Nat.Coprime r m) :
    (∀ α β, (grs k hk f hf).π α = 1 →
        GRS.delta (Fsh5 (AdjoinRoot f) m r) α β ≤ 2 * Fintype.card (AdjoinRoot (fbar k hk f))) ∧
    (∀ g : (AdjoinRoot f)[X], g.map (grs k hk f hf).π = F5 _ m r → ∀ α, (grs k hk f hf).π α = 1 →
        ∃ β, 2 * Fintype.card (AdjoinRoot (fbar k hk f)) ≤ GRS.delta g α β) ∧
    (∃ α β, (grs k hk f hf).π α = 1 ∧
        2 * Fintype.card (AdjoinRoot (fbar k hk f)) < GRS.delta (F5 (AdjoinRoot f) m r) α β) := by
  obtain ⟨hc, hK⟩ := grs_card k hk f hf
  rw [hdeg] at hK
  set S := grs k hk f hf
  have hcard : Fintype.card (AdjoinRoot f) = Fintype.card (AdjoinRoot (fbar k hk f)) ^ S.k := hc
  exact ⟨fun α β hα => S.fam5_upper hcard m r hm5 hr5 hrm hodd hmodd hK hcop α β hα,
    fun g hg α hα => S.fam5_lower_all hcard m r hm5 hr5 hrm hodd hK hcop g hg α hα,
    S.fam5_natural hcard m r hm5 hr5 hrm hodd hK hcop⟩

end main

end APN2
