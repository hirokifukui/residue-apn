import Apn2R03.Coherent
import Apn2R03.GRCompat

/-!
# The concrete tower ℤ[t]/(g) → GR(2^k, m), k ≥ 3 (Claude, 2026-10-25, R05b)

For a monic g ∈ ℤ[X] whose reduction ḡ ∈ F_2[X] is irreducible (of degree m), the rings
R_j = (ℤ/2^(j+3))[X]/(g mod 2^(j+3)) = GR(2^(j+3), m) form a `GRS.Tower` over the common coefficient ring
ℤ[X]/(g), with the common residue field F_2[X]/(ḡ):
* `towerGR`           : the tower (levels j + 3, reductions to level 3, coefficient maps from ℤ[X]/(g));
* `towerGR_card`      : |R_j| = |F_2[X]/(ḡ)|^(j+3);
* `coherent_family_GR`: Corollary CL2 with the quantifier over all levels, on the concrete Galois rings:
  some F over ℤ[X]/(g) reduces to an optimal lift at level 3 and at every level ≥ 4 iff μ = 0 or Z ≠ ∅.
This instantiates `coherent_family` and shows that the abstract tower hypothesis is satisfied by GR.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Polynomial

section Tower

variable (g : ℤ[X])

/-- g modulo 2^(j+3) -/
noncomputable abbrev gk (j : ℕ) : (ZMod (2 ^ (j + 3)))[X] := g.map (Int.castRingHom _)

/-- g modulo 2 -/
noncomputable abbrev g2 : (ZMod 2)[X] := g.map (Int.castRingHom _)

theorem fbar_gk (j : ℕ) : fbar (j + 3) (by omega) (gk g j) = g2 g := by
  unfold fbar gk g2
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

instance fact_gk [hirr : Fact (Irreducible (g2 g))] (j : ℕ) :
    Fact (Irreducible (fbar (j + 3) (by omega) (gk g j))) :=
  ⟨by rw [fbar_gk]; exact hirr.out⟩

variable [Fact (Irreducible (g2 g))]

theorem gk_monic (hg : g.Monic) (j : ℕ) : (gk g j).Monic := hg.map _

/-- the level-(j+3) structure with the common residue field F_2[X]/(ḡ) -/
noncomputable def Sgr (hg : g.Monic) (j : ℕ) : GRS (AdjoinRoot (gk g j)) (AdjoinRoot (g2 g)) :=
  (grs (j + 3) (Nat.le_add_left 3 j) (gk g j) (gk_monic g hg j)).ofEquiv
    (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ (fbar_gk g j)).toRingEquiv

theorem Sgr_k (hg : g.Monic) (j : ℕ) : (Sgr g hg j).k = j + 3 := rfl

theorem Sgr_pi_mk (hg : g.Monic) (j : ℕ) (p : (ZMod (2 ^ (j + 3)))[X]) :
    (Sgr g hg j).π (AdjoinRoot.mk (gk g j) p) = AdjoinRoot.mk (g2 g) (p.map (red (j + 3) (by omega))) := by
  show (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ (fbar_gk g j)) (piGR (j + 3) (by omega) (gk g j) _) = _
  rw [piGR_mk, algEquivOfEq_mk]

/-- reduction of coefficients ℤ/2^(j+4) → ℤ/8 -/
noncomputable def cdown (j : ℕ) : ZMod (2 ^ (j + 1 + 3)) →+* ZMod (2 ^ (0 + 3)) :=
  ZMod.castHom (pow_dvd_pow 2 (by omega)) _

theorem gk_map_cdown (j : ℕ) : (gk g (j + 1)).map (cdown j) = gk g 0 := by
  unfold gk
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

theorem eval₂_root_down (j : ℕ) :
    (gk g (j + 1)).eval₂ ((AdjoinRoot.of (gk g 0)).comp (cdown j)) (AdjoinRoot.root (gk g 0)) = 0 := by
  rw [← Polynomial.eval₂_map, gk_map_cdown]; exact AdjoinRoot.eval₂_root _

/-- GR(2^(j+4), m) → GR(8, m) -/
noncomputable def psiDown (j : ℕ) : AdjoinRoot (gk g (j + 1)) →+* AdjoinRoot (gk g 0) :=
  AdjoinRoot.lift _ _ (eval₂_root_down g j)

theorem psiDown_mk (j : ℕ) (p : (ZMod (2 ^ (j + 1 + 3)))[X]) :
    psiDown g j (AdjoinRoot.mk (gk g (j + 1)) p) = AdjoinRoot.mk (gk g 0) (p.map (cdown j)) := by
  unfold psiDown
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
  rfl

/-- the compatibility datum from level j + 4 to level 3 -/
noncomputable def compatDown (hg : g.Monic) (j : ℕ) : GRS.Compat (Sgr g hg (j + 1)) (Sgr g hg 0) where
  ψ := psiDown g j
  hπ := by
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [psiDown_mk, Sgr_pi_mk, Sgr_pi_mk, Polynomial.map_map]
    congr 2
    exact RingHom.ext_zmod _ _

theorem eval₂_root_up (j : ℕ) :
    g.eval₂ ((AdjoinRoot.of (gk g j)).comp (Int.castRingHom _)) (AdjoinRoot.root (gk g j)) = 0 := by
  rw [← Polynomial.eval₂_map]; exact AdjoinRoot.eval₂_root _

/-- ℤ[X]/(g) → GR(2^(j+3), m) -/
noncomputable def phiUp (j : ℕ) : AdjoinRoot g →+* AdjoinRoot (gk g j) :=
  AdjoinRoot.lift _ _ (eval₂_root_up g j)

theorem phiUp_mk (j : ℕ) (p : ℤ[X]) :
    phiUp g j (AdjoinRoot.mk g p) = AdjoinRoot.mk (gk g j) (p.map (Int.castRingHom _)) := by
  unfold phiUp
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
  rfl

/-- **The Galois rings GR(2^(j+3), m) form a coherent tower over ℤ[X]/(g).** -/
noncomputable def towerGR (hg : g.Monic) :
    GRS.Tower (fun j => AdjoinRoot (gk g j)) (AdjoinRoot (g2 g)) (AdjoinRoot g) where
  S := Sgr g hg
  hlev := Sgr_k g hg
  C := compatDown g hg
  φ := phiUp g
  hφ := by
    intro j
    apply RingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    show psiDown g j (phiUp g (j + 1) (AdjoinRoot.mk g p)) = phiUp g 0 (AdjoinRoot.mk g p)
    rw [phiUp_mk, psiDown_mk, phiUp_mk, Polynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  surj0 := by
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨p', hp'⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod (2 ^ (0 + 3))))
      (ZMod.intCast_surjective) p
    exact ⟨AdjoinRoot.mk g p', by show phiUp g 0 _ = _; rw [phiUp_mk, hp']⟩

variable [∀ j, Fintype (AdjoinRoot (gk g j))] [∀ j, DecidableEq (AdjoinRoot (gk g j))]
variable [Fintype (AdjoinRoot (g2 g))] [DecidableEq (AdjoinRoot (g2 g))]

theorem towerGR_card (hg : g.Monic) (j : ℕ) :
    Fintype.card (AdjoinRoot (gk g j)) = Fintype.card (AdjoinRoot (g2 g)) ^ ((towerGR g hg).S j).k ∧
      Fintype.card (AdjoinRoot (g2 g)) = 2 ^ g.natDegree := by
  let e := (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ (fbar_gk g j)).toEquiv
  letI : Fintype (AdjoinRoot (fbar (j + 3) (Nat.le_add_left 3 j) (gk g j))) := Fintype.ofEquiv _ e.symm
  obtain ⟨hR, hK⟩ := grs_card (j + 3) (Nat.le_add_left 3 j) (gk g j) (gk_monic g hg j)
  have hKK : Fintype.card (AdjoinRoot (fbar (j + 3) (Nat.le_add_left 3 j) (gk g j))) =
      Fintype.card (AdjoinRoot (g2 g)) := Fintype.card_congr e
  refine ⟨?_, ?_⟩
  · show _ = _ ^ (j + 3)
    rw [hR, hKK]
  · haveI : Fact (1 < 2 ^ (j + 3)) := ⟨Nat.one_lt_two_pow (by omega)⟩
    rw [← hKK, hK, (hg.natDegree_map (Int.castRingHom (ZMod (2 ^ (j + 3)))))]

/-- **Corollary CL2 on the concrete Galois rings, with the quantifier over all levels.** -/
theorem coherent_family_GR (hg : g.Monic) (m : ℕ) (hdeg : g.natDegree = m) (hm2 : 2 ≤ m)
    (F0 : (AdjoinRoot g)[X]) (ρ μ : AdjoinRoot (g2 g))
    (H : ((towerGR g hg).S 0).Hyp (F0.map ((towerGR g hg).φ 0)) ρ μ) :
    (∃ F : (AdjoinRoot g)[X],
        (F.map ((towerGR g hg).φ 0)).map ((towerGR g hg).S 0).π =
          (F0.map ((towerGR g hg).φ 0)).map ((towerGR g hg).S 0).π ∧
        (∀ α β, ((towerGR g hg).S 0).π α = ρ →
          GRS.delta (F.map ((towerGR g hg).φ 0)) α β ≤
            ((towerGR g hg).S 0).vmin3 (F.map ((towerGR g hg).φ 0)) ρ) ∧
        ∀ j, ∀ α β, ((towerGR g hg).S (j + 1)).π α = ρ →
          GRS.delta (F.map ((towerGR g hg).φ (j + 1))) α β ≤
            ((towerGR g hg).S (j + 1)).vmin4 (F.map ((towerGR g hg).φ (j + 1))) ρ μ) ↔
      (μ = 0 ∨ ∃ a, ((towerGR g hg).S 0).Lam (F0.map ((towerGR g hg).φ 0)) ρ a = 0) := by
  have hK := (towerGR_card g hg 0).2
  rw [hdeg] at hK
  have hq : 2 < Fintype.card (AdjoinRoot (g2 g)) := by
    rw [hK]; calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  exact GRS.coherent_family (towerGR g hg) (fun j => (towerGR_card g hg j).1) m hK hq F0 ρ μ H

end Tower

end APN2

#print axioms APN2.towerGR
#print axioms APN2.towerGR_card
#print axioms APN2.coherent_family_GR
