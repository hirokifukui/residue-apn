import Apn2R03.CrossLevel
import Apn2R03.MainGR2

/-!
# Cross-level optimality on the concrete rings GR(2^k, m) → GR(8, m) (Claude, 2026-10-25, R04-09)

For a monic f ∈ (ℤ/2^k)[X] with irreducible reduction, put f₃ = f mod 8.  Reduction of coefficients
gives ψ : GR(2^k, m) = (ℤ/2^k)[X]/(f) → (ℤ/8)[X]/(f₃) = GR(8, m), compatible with the residue maps
(after identifying the two residue fields F_2[X]/(f̄) by `AdjoinRoot.algEquivOfEq`).
`F.map ψ` is the compatible level-8 lift of a level-2^k lift F (same integer coefficients mod 8).

* `cross_level_stay_GR`   : if F mod 8 minimizes Δ_exc on GR(8, m), then F minimizes Δ_exc on
                            GR(2^k, m) (k ≥ 4) iff A_F has no zero;
* `cross_level_exists_GR` : a lift minimizing on GR(2^k, m) whose reduction mod 8 also minimizes
                            exists iff μ = 0 or Λ has a zero.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

/-- transport the residue field of an abstract Galois ring along a ring isomorphism -/
def GRS.ofEquiv {R K K' : Type*} [CommRing R] [Field K] [Field K'] (S : GRS R K') (e : K' ≃+* K) :
    GRS R K where
  π := e.toRingHom.comp S.π
  surj := e.surjective.comp S.surj
  k := S.k
  hk := S.hk
  ker2 := fun x => by
    show e (S.π x) = 0 ↔ _
    rw [← S.ker2 x]
    constructor
    · intro h; exact e.injective (by rw [h, map_zero])
    · intro h; rw [h, map_zero]
  nil := S.nil
  tors := S.tors

theorem algEquivOfEq_mk (g₁ g₂ : (ZMod 2)[X]) (h : g₁ = g₂) (p : (ZMod 2)[X]) :
    AdjoinRoot.algEquivOfEq (ZMod 2) g₁ g₂ h (AdjoinRoot.mk g₁ p) = AdjoinRoot.mk g₂ p := by
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq]
  have := Polynomial.aeval_algHom_apply (AdjoinRoot.algEquivOfEq (ZMod 2) g₁ g₂ h).toAlgHom
    (AdjoinRoot.root g₁) p
  convert this.symm using 2
  exact congrArg _ (AdjoinRoot.algEquivOfEq_root (R := ZMod 2) g₁ g₂ h).symm

section GR

variable (k : ℕ) (hk : 3 ≤ k) (f : (ZMod (2 ^ k))[X])

/-- reduction ℤ/2^k → ℤ/8 -/
noncomputable def c8 : ZMod (2 ^ k) →+* ZMod (2 ^ 3) := ZMod.castHom (pow_dvd_pow 2 hk) _

/-- f mod 8 -/
noncomputable abbrev f3 : (ZMod (2 ^ 3))[X] := f.map (c8 k hk)

theorem map_red_c8 (p : (ZMod (2 ^ k))[X]) :
    (p.map (c8 k hk)).map (red 3 (by omega)) = p.map (red k (by omega)) := by
  rw [Polynomial.map_map]; congr 1; exact RingHom.ext_zmod _ _

theorem fbar3_eq : fbar 3 le_rfl (f3 k hk f) = fbar k hk f := map_red_c8 k hk f

theorem f3_monic (hf : f.Monic) : (f3 k hk f).Monic := hf.map _

theorem eval₂_root_c8 :
    f.eval₂ ((AdjoinRoot.of (f3 k hk f)).comp (c8 k hk)) (AdjoinRoot.root (f3 k hk f)) = 0 := by
  rw [← Polynomial.eval₂_map]; exact AdjoinRoot.eval₂_root _

/-- coefficient reduction GR(2^k, m) → GR(8, m) -/
noncomputable def psiGR : AdjoinRoot f →+* AdjoinRoot (f3 k hk f) :=
  AdjoinRoot.lift _ _ (eval₂_root_c8 k hk f)

theorem psiGR_mk (p : (ZMod (2 ^ k))[X]) :
    psiGR k hk f (AdjoinRoot.mk f p) = AdjoinRoot.mk (f3 k hk f) (p.map (c8 k hk)) := by
  unfold psiGR
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
  rfl

variable [Fact (Irreducible (fbar k hk f))]

instance fact_fbar3 : Fact (Irreducible (fbar 3 le_rfl (f3 k hk f))) :=
  ⟨by rw [fbar3_eq]; exact Fact.out⟩

/-- GR(8, m) as an abstract Galois ring with residue field F_2[X]/(f̄) -/
noncomputable def S3GR (hf : f.Monic) : GRS (AdjoinRoot (f3 k hk f)) (AdjoinRoot (fbar k hk f)) :=
  (grs 3 le_rfl (f3 k hk f) (f3_monic k hk f hf)).ofEquiv
    (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ (fbar3_eq k hk f)).toRingEquiv

theorem S3GR_k (hf : f.Monic) : (S3GR k hk f hf).k = 3 := rfl

theorem S3GR_pi_mk (hf : f.Monic) (q : (ZMod (2 ^ 3))[X]) :
    (S3GR k hk f hf).π (AdjoinRoot.mk (f3 k hk f) q) =
      AdjoinRoot.mk (fbar k hk f) (q.map (red 3 (by omega))) := by
  show (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ (fbar3_eq k hk f)) (piGR 3 le_rfl (f3 k hk f) _) = _
  rw [piGR_mk, algEquivOfEq_mk]

/-- the compatibility datum for GR(2^k, m) → GR(8, m) -/
noncomputable def compatGR (hf : f.Monic) : GRS.Compat (grs k hk f hf) (S3GR k hk f hf) where
  ψ := psiGR k hk f
  hπ := by
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [psiGR_mk, S3GR_pi_mk, map_red_c8]
    show _ = piGR k hk f (AdjoinRoot.mk f p)
    rw [piGR_mk]

variable [Fintype (AdjoinRoot f)] [DecidableEq (AdjoinRoot f)]
variable [Fintype (AdjoinRoot (fbar k hk f))] [DecidableEq (AdjoinRoot (fbar k hk f))]
variable [Fintype (AdjoinRoot (f3 k hk f))] [DecidableEq (AdjoinRoot (f3 k hk f))]

theorem card_GR8 (hf : f.Monic) :
    Fintype.card (AdjoinRoot (f3 k hk f)) = Fintype.card (AdjoinRoot (fbar k hk f)) ^ 3 := by
  haveI : Fintype (AdjoinRoot (fbar 3 le_rfl (f3 k hk f))) :=
    @Fintype.ofFinite _ (finite_bar _ ((f3_monic k hk f hf).map _))
  obtain ⟨h3, hK3⟩ := grs_card 3 le_rfl (f3 k hk f) (f3_monic k hk f hf)
  obtain ⟨_, hK⟩ := grs_card k hk f hf
  rw [h3, hK3, hK]
  haveI : Fact (1 < 2 ^ 3) := ⟨by norm_num⟩
  show (2 ^ (f.map (c8 k hk)).natDegree) ^ 3 = _
  rw [hf.natDegree_map]

/-- **Cross-level corollary (i) on GR**: a lift whose reduction mod 8 minimizes Δ_exc on GR(8, m)
minimizes Δ_exc on GR(2^k, m) (k ≥ 4) iff A_F has no zero. -/
theorem cross_level_stay_GR (hf : f.Monic) (hk4 : 4 ≤ k) (m : ℕ) (hdeg : f.natDegree = m) (hm2 : 2 ≤ m)
    (F : (AdjoinRoot f)[X]) (ρ μ : AdjoinRoot (fbar k hk f)) (H : (grs k hk f hf).Hyp F ρ μ)
    (h8 : ∀ α β, (S3GR k hk f hf).π α = ρ →
      GRS.delta (F.map (psiGR k hk f)) α β ≤ (S3GR k hk f hf).vmin3 (F.map (psiGR k hk f)) ρ) :
    (∀ α β, (grs k hk f hf).π α = ρ → GRS.delta F α β ≤ (grs k hk f hf).vmin4 F ρ μ) ↔
      ∀ a, (grs k hk f hf).Afun F ρ a ≠ 0 := by
  obtain ⟨hc, hK⟩ := grs_card k hk f hf
  rw [hdeg] at hK
  have hq : 2 < Fintype.card (AdjoinRoot (fbar k hk f)) := by
    rw [hK]; calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  exact GRS.cross_level_stay (compatGR k hk f hf) rfl hk4 (card_GR8 k hk f hf) hc m hK hq F ρ μ H h8

/-- **Cross-level corollary (ii) on GR**: a lift minimizing Δ_exc on GR(2^k, m) (k ≥ 4) whose
reduction mod 8 also minimizes on GR(8, m) exists iff μ = 0 or Λ has a zero. -/
theorem cross_level_exists_GR (hf : f.Monic) (hk4 : 4 ≤ k) (m : ℕ) (hdeg : f.natDegree = m) (hm2 : 2 ≤ m)
    (F0 : (AdjoinRoot f)[X]) (ρ μ : AdjoinRoot (fbar k hk f)) (H : (grs k hk f hf).Hyp F0 ρ μ) :
    (∃ F : (AdjoinRoot f)[X], F.map (grs k hk f hf).π = F0.map (grs k hk f hf).π ∧
        (∀ α β, (S3GR k hk f hf).π α = ρ →
          GRS.delta (F.map (psiGR k hk f)) α β ≤ (S3GR k hk f hf).vmin3 (F.map (psiGR k hk f)) ρ) ∧
        (∀ α β, (grs k hk f hf).π α = ρ → GRS.delta F α β ≤ (grs k hk f hf).vmin4 F ρ μ)) ↔
      (μ = 0 ∨ ∃ a, (grs k hk f hf).Lam F0 ρ a = 0) := by
  obtain ⟨hc, hK⟩ := grs_card k hk f hf
  rw [hdeg] at hK
  have hq : 2 < Fintype.card (AdjoinRoot (fbar k hk f)) := by
    rw [hK]; calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  exact GRS.cross_level_exists (compatGR k hk f hf) rfl hk4 (card_GR8 k hk f hf) hc m hK hq F0 ρ μ H

end GR

end APN2

#print axioms APN2.cross_level_stay_GR
#print axioms APN2.cross_level_exists_GR
