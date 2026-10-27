import Apn2R03.MainK3
import Apn2R03.MainK4

/-!
# Cross-level optimality (Claude, 2026-10-25, R04-01/02/09)

Two Galois-ring structures with the same residue field, `Sk : GRS Rk K` (level k ≥ 4) and
`S3 : GRS R3 K` (level 3), linked by a ring hom `ψ : Rk → R3` over the residue maps
(`Compat`; for GR this is reduction mod 8, and `f.map ψ` is the compatible lift at level 3).

* `A_compat`, `E_compat`, `Lam_compat`, `hyp_compat` : the invariants of `f.map ψ` at level 3
  are those of `f` at level k (they only depend on f mod 8).
* `cross_level_stay`  : if `f.map ψ` minimizes Δ_exc at level 3, then `f` minimizes Δ_exc at level k
  iff A_f has no zero.  (This replaces the false sentence "a lift attaining the value at level 8
  attains it at every level".)
* `cross_level_exists`: a lift minimizing at level k whose level-3 image also minimizes exists
  iff μ = 0 or Λ has a zero (Z ≠ ∅).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {Rk R3 K : Type*} [CommRing Rk] [CommRing R3] [Field K]

/-- a level-k structure and a level-3 structure with the same residue field, linked by ψ -/
structure Compat (Sk : GRS Rk K) (S3 : GRS R3 K) where
  ψ : Rk →+* R3
  hπ : ∀ x, S3.π (ψ x) = Sk.π x

variable {Sk : GRS Rk K} {S3 : GRS R3 K}

theorem eval_map_hom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B) (p : A[X]) (x : A) :
    (p.map ψ).eval (ψ x) = ψ (p.eval x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem Compat.map_map (C : Compat Sk S3) (f : Rk[X]) : (f.map C.ψ).map S3.π = f.map Sk.π := by
  rw [Polynomial.map_map]
  congr 1
  ext x
  exact C.hπ x

theorem Lam_compat (C : Compat Sk S3) (f : Rk[X]) (ρ a : K) :
    S3.Lam (f.map C.ψ) ρ a = Sk.Lam f ρ a := by
  unfold Lam; rw [C.map_map]

theorem hyp_compat (C : Compat Sk S3) (f : Rk[X]) (ρ μ : K) (H : Sk.Hyp f ρ μ) :
    S3.Hyp (f.map C.ψ) ρ μ :=
  ⟨H.hρ, by rw [C.map_map]; exact H.hper, by rw [C.map_map]; exact H.hμ, by rw [C.map_map]; exact H.hdp⟩

theorem A_compat (C : Compat Sk S3) (f : Rk[X]) (ρ : K)
    (hper : ∀ a, (f.map Sk.π).derivative.eval (a + ρ) = (f.map Sk.π).derivative.eval a) (a : K) :
    S3.Afun (f.map C.ψ) ρ a = Sk.Afun f ρ a := by
  obtain ⟨g, hg, hgA⟩ := Sk.A_spec f ρ hper (Sk.L a) (Sk.L ρ) a (Sk.pi_L a) (Sk.pi_L ρ)
  have hper' : ∀ a, ((f.map C.ψ).map S3.π).derivative.eval (a + ρ) =
      ((f.map C.ψ).map S3.π).derivative.eval a := by rw [C.map_map]; exact hper
  obtain ⟨g', hg', hgA'⟩ := S3.A_spec (f.map C.ψ) ρ hper' (C.ψ (Sk.L a)) (C.ψ (Sk.L ρ)) a
    (by rw [C.hπ, Sk.pi_L]) (by rw [C.hπ, Sk.pi_L])
  rw [← hgA', ← hgA, ← C.hπ g]
  apply S3.pi_eq_of_two_mul_eq
  rw [← hg', Polynomial.derivative_map, ← map_add, eval_map_hom, eval_map_hom, ← map_sub, hg,
    map_mul, map_ofNat]

theorem Sx_map (ψ : Rk →+* R3) (f : Rk[X]) (x τ : Rk) :
    Sx (f.map ψ) (ψ x) (ψ τ) = ψ (Sx f x τ) := by
  unfold Sx
  have e1 : ψ x + 2 * ψ τ = ψ (x + 2 * τ) := by rw [map_add, map_mul, map_ofNat]
  have e2 : ψ x + ψ τ = ψ (x + τ) := by rw [map_add]
  rw [e1, e2, eval_map_hom, eval_map_hom, eval_map_hom, map_add, map_sub, map_mul, map_ofNat]

theorem E_compat (C : Compat Sk S3) (f : Rk[X]) (ρ : K)
    (hper : ∀ a, (f.map Sk.π).derivative.eval (a + ρ) = (f.map Sk.π).derivative.eval a) (a : K)
    (hL : Sk.Lam f ρ a = 0) :
    S3.Efun (f.map C.ψ) ρ a = Sk.Efun f ρ a := by
  obtain ⟨c, hc, hcE⟩ := Sk.E_spec f ρ hper (Sk.L a) (Sk.L ρ) a (Sk.pi_L a) (Sk.pi_L ρ) hL
  have hper' : ∀ a, ((f.map C.ψ).map S3.π).derivative.eval (a + ρ) =
      ((f.map C.ψ).map S3.π).derivative.eval a := by rw [C.map_map]; exact hper
  obtain ⟨c', hc', hcE'⟩ := S3.E_spec (f.map C.ψ) ρ hper' (C.ψ (Sk.L a)) (C.ψ (Sk.L ρ)) a
    (by rw [C.hπ, Sk.pi_L]) (by rw [C.hπ, Sk.pi_L]) (by rw [Lam_compat]; exact hL)
  rw [← hcE', ← hcE, ← C.hπ c]
  apply S3.pi_eq_of_four_mul_eq
  rw [← hc', Sx_map, hc, map_mul, map_ofNat]

variable [Fintype Rk] [DecidableEq Rk] [Fintype R3] [DecidableEq R3] [Fintype K] [DecidableEq K]

/-- **Cross-level corollary (i)**: a level-3 minimizer stays a minimizer at level k ≥ 4 iff A has no zero. -/
theorem cross_level_stay (C : Compat Sk S3) (hk3 : S3.k = 3) (hk4 : 4 ≤ Sk.k)
    (hc3 : Fintype.card R3 = Fintype.card K ^ S3.k) (hck : Fintype.card Rk = Fintype.card K ^ Sk.k)
    (m : ℕ) (hm : Fintype.card K = 2 ^ m) (hq : 2 < Fintype.card K)
    (f : Rk[X]) (ρ μ : K) (H : Sk.Hyp f ρ μ)
    (h8 : ∀ α β, S3.π α = ρ → delta (f.map C.ψ) α β ≤ S3.vmin3 (f.map C.ψ) ρ) :
    (∀ α β, Sk.π α = ρ → delta f α β ≤ Sk.vmin4 f ρ μ) ↔ ∀ a, Sk.Afun f ρ a ≠ 0 := by
  have H3 := hyp_compat C f ρ μ H
  obtain ⟨_, _, c3⟩ := (S3.minimizers_k3 hk3 hc3 m hm hq _ ρ μ H3).mp h8
  rw [Sk.minimizers_k4 hck hk4 m hm hq f ρ μ H]
  constructor
  · exact fun h => h.1
  · intro hA0
    refine ⟨hA0, fun hμ a hLa => ?_⟩
    have h := c3 hμ a (by rw [Lam_compat]; exact hLa) (by rw [A_compat C f ρ H.hper]; exact hA0 a)
    rwa [A_compat C f ρ H.hper, E_compat C f ρ H.hper a hLa] at h

/-- **Cross-level corollary (ii)**: some lift is optimal at level k and has an optimal level-3 image
iff μ = 0 or Λ has a zero. -/
theorem cross_level_exists (C : Compat Sk S3) (hk3 : S3.k = 3) (hk4 : 4 ≤ Sk.k)
    (hc3 : Fintype.card R3 = Fintype.card K ^ S3.k) (hck : Fintype.card Rk = Fintype.card K ^ Sk.k)
    (m : ℕ) (hm : Fintype.card K = 2 ^ m) (hq : 2 < Fintype.card K)
    (f0 : Rk[X]) (ρ μ : K) (H : Sk.Hyp f0 ρ μ) :
    (∃ f : Rk[X], f.map Sk.π = f0.map Sk.π ∧
        (∀ α β, S3.π α = ρ → delta (f.map C.ψ) α β ≤ S3.vmin3 (f.map C.ψ) ρ) ∧
        (∀ α β, Sk.π α = ρ → delta f α β ≤ Sk.vmin4 f ρ μ)) ↔
      (μ = 0 ∨ ∃ a, Sk.Lam f0 ρ a = 0) := by
  constructor
  · rintro ⟨f, hf, h3opt, hkopt⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hμ, hZ⟩ := hcon
    have Hf := Sk.hyp_of_map_eq f0 f hf ρ μ H
    have hAz := ((Sk.minimizers_k4 hck hk4 m hm hq f ρ μ Hf).mp hkopt).1
    obtain ⟨_, c2, _⟩ :=
      (S3.minimizers_k3 hk3 hc3 m hm hq _ ρ μ (hyp_compat C f ρ μ Hf)).mp h3opt
    have h0 := c2 hμ (fun a => by rw [Lam_compat, Sk.Lam_of_map_eq f0 f hf]; exact hZ a) 0
    rw [A_compat C f ρ Hf.hper] at h0
    exact hAz 0 h0
  · intro hcase
    obtain ⟨g, hg, hgopt⟩ := Sk.minimax_k4_attain hck m hm f0 ρ μ H
    have Hg := Sk.hyp_of_map_eq f0 g hg ρ μ H
    have hkopt : ∀ α β, Sk.π α = ρ → delta g α β ≤ Sk.vmin4 g ρ μ := by
      intro α β hα; rw [Sk.vmin4_of_map_eq f0 g hg]; exact hgopt α β hα
    obtain ⟨hAz, hχ⟩ := (Sk.minimizers_k4 hck hk4 m hm hq g ρ μ Hg).mp hkopt
    refine ⟨g, hg, ?_, hkopt⟩
    apply (S3.minimizers_k3 hk3 hc3 m hm hq _ ρ μ (hyp_compat C g ρ μ Hg)).mpr
    refine ⟨fun _ a => by rw [A_compat C g ρ Hg.hper]; exact hAz a, fun hμ hZ3 => ?_, fun hμ a hL3 _ => ?_⟩
    · exfalso
      rcases hcase with h | ⟨a, ha⟩
      · exact hμ h
      · exact hZ3 a (by rw [Lam_compat, Sk.Lam_of_map_eq f0 g hg]; exact ha)
    · have hLg : Sk.Lam g ρ a = 0 := by rw [← Lam_compat C]; exact hL3
      rw [A_compat C g ρ Hg.hper, E_compat C g ρ Hg.hper a hLg]
      exact hχ hμ a hLg

end GRS

end APN2

#print axioms APN2.GRS.A_compat
#print axioms APN2.GRS.E_compat
#print axioms APN2.GRS.cross_level_stay
#print axioms APN2.GRS.cross_level_exists
