import Apn2R03.GRCompat

/-!
# Stability modulo 8, literal form (paper Theorem S3) (Claude, 2026-10-25)

If A_F has no zero, then for every exceptional α (π α = ρ) and every β,
  δ_F(α, β) at level k  =  δ_{F mod 8}(ψ α, ψ β) at level 3.

Proof: class by class, `cc_k(a) = cc_3(a)`.  The gate `G(x_a) ∈ 4R` is transported both ways by ψ
(`four_dvd_iff`, proved from the axioms alone: no extra hypothesis on ker ψ is needed), the constant
c_a and the invariants A, μ are preserved, so `cc_formula` / `cc_zero` give the same value on both
levels; then sum (`delta_eq_sum`).  Both μ ≠ 0 and μ = 0 are covered (μ is arbitrary).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {Rk R3 K : Type*} [CommRing Rk] [CommRing R3] [Field K]
variable {Sk : GRS Rk K} {S3 : GRS R3 K}

/-- the gate `y ∈ 4R` is reflected by ψ -/
theorem Compat.four_dvd_iff (C : Compat Sk S3) (y : Rk) :
    (∃ c, C.ψ y = 4 * c) ↔ ∃ c, y = 4 * c := by
  constructor
  · rintro ⟨c, hc⟩
    have h0 : Sk.π y = 0 := by
      rw [← C.hπ, hc, map_mul, show (4 : R3) = 2 * 2 by norm_num, map_mul, S3.pi_two, zero_mul,
        zero_mul]
    obtain ⟨y1, rfl⟩ := (Sk.ker2 y).mp h0
    have h2 : 2 * C.ψ y1 = 2 * (2 * c) := by
      rw [map_mul, map_ofNat] at hc
      rw [hc]; ring
    have h3 := S3.pi_eq_of_two_mul_eq h2
    rw [S3.pi_two_mul, C.hπ] at h3
    obtain ⟨y2, rfl⟩ := (Sk.ker2 y1).mp h3
    exact ⟨y2, by ring⟩
  · rintro ⟨c, rfl⟩
    exact ⟨C.ψ c, by rw [map_mul, map_ofNat]⟩

theorem Gpoly_eval_map (ψ : Rk →+* R3) (f : Rk[X]) (α β x : Rk) :
    (Gpoly (f.map ψ) (ψ α) (ψ β)).eval (ψ x) = ψ ((Gpoly f α β).eval x) := by
  rw [Gpoly_eval, Gpoly_eval, ← map_add, eval_map_hom, eval_map_hom, map_sub, map_sub]

variable [Fintype Rk] [DecidableEq Rk] [Fintype R3] [DecidableEq R3] [Fintype K] [DecidableEq K]

/-- class counts agree on both levels when A has no zero -/
theorem cc_stable (C : Compat Sk S3)
    (hc3 : Fintype.card R3 = Fintype.card K ^ S3.k) (hck : Fintype.card Rk = Fintype.card K ^ Sk.k)
    (f : Rk[X]) (ρ μ : K) (H : Sk.Hyp f ρ μ) (hA : ∀ a, Sk.Afun f ρ a ≠ 0)
    (α β : Rk) (hα : Sk.π α = ρ) (a : K) :
    Sk.cc f α β a = S3.cc (f.map C.ψ) (C.ψ α) (C.ψ β) a := by
  have H3 := hyp_compat C f ρ μ H
  set xa := Sk.L a with hxa_def
  have hxa : Sk.π xa = a := Sk.pi_L a
  have hxa3 : S3.π (C.ψ xa) = a := by rw [C.hπ, hxa]
  have hα3 : S3.π (C.ψ α) = ρ := by rw [C.hπ, hα]
  by_cases hg : ∃ c, (Gpoly f α β).eval xa = 4 * c
  · obtain ⟨c, hc⟩ := hg
    have hc3' : (Gpoly (f.map C.ψ) (C.ψ α) (C.ψ β)).eval (C.ψ xa) = 4 * C.ψ c := by
      rw [Gpoly_eval_map, hc, map_mul, map_ofNat]
    have e1 := Sk.cc_formula hck f ρ μ H.hper H.hμ α β xa c hα hc (by rw [hxa]; exact hA a)
    have hA3 : S3.Afun (f.map C.ψ) ρ (S3.π (C.ψ xa)) ≠ 0 := by
      rw [hxa3, A_compat C f ρ H.hper]; exact hA a
    have e3 := S3.cc_formula hc3 (f.map C.ψ) ρ μ H3.hper H3.hμ (C.ψ α) (C.ψ β) (C.ψ xa) (C.ψ c)
      hα3 hc3' hA3
    rw [hxa] at e1
    rw [hxa3, A_compat C f ρ H.hper, C.hπ] at e3
    rw [e1, e3]
  · have e1 := Sk.cc_zero f ρ H.hper α β xa hα hg
    have hg3 : ¬ ∃ c, (Gpoly (f.map C.ψ) (C.ψ α) (C.ψ β)).eval (C.ψ xa) = 4 * c := by
      rw [Gpoly_eval_map, C.four_dvd_iff]; exact hg
    have e3 := S3.cc_zero (f.map C.ψ) ρ H3.hper (C.ψ α) (C.ψ β) (C.ψ xa) hα3 hg3
    rw [hxa] at e1
    rw [hxa3] at e3
    rw [e1, e3]

/-- **Theorem S3 (stability modulo 8, literal form)**: if A_F has no zero, then for every
exceptional α and every β, δ_F(α, β) at level k equals δ_{F.map ψ}(ψ α, ψ β) at level 3. -/
theorem delta_stable_mod8 (C : Compat Sk S3)
    (hc3 : Fintype.card R3 = Fintype.card K ^ S3.k) (hck : Fintype.card Rk = Fintype.card K ^ Sk.k)
    (f : Rk[X]) (ρ μ : K) (H : Sk.Hyp f ρ μ) (hA : ∀ a, Sk.Afun f ρ a ≠ 0)
    (α β : Rk) (hα : Sk.π α = ρ) :
    delta f α β = delta (f.map C.ψ) (C.ψ α) (C.ψ β) := by
  rw [Sk.delta_eq_sum, S3.delta_eq_sum]
  exact Finset.sum_congr rfl fun a _ => cc_stable C hc3 hck f ρ μ H hA α β hα a

end GRS

section GR

variable (k : ℕ) (hk : 3 ≤ k) (f : (ZMod (2 ^ k))[X])
variable [Fact (Irreducible (fbar k hk f))]
variable [Fintype (AdjoinRoot f)] [DecidableEq (AdjoinRoot f)]
variable [Fintype (AdjoinRoot (fbar k hk f))] [DecidableEq (AdjoinRoot (fbar k hk f))]
variable [Fintype (AdjoinRoot (f3 k hk f))] [DecidableEq (AdjoinRoot (f3 k hk f))]

/-- **Theorem S3 on GR(2^k, m) → GR(8, m)**: if A_F has no zero, then for every exceptional α and
every β, δ_F(α, β) on GR(2^k, m) equals δ_{F mod 8}(α mod 8, β mod 8) on GR(8, m). -/
theorem delta_stable_mod8_GR (hf : f.Monic)
    (F : (AdjoinRoot f)[X]) (ρ μ : AdjoinRoot (fbar k hk f)) (H : (grs k hk f hf).Hyp F ρ μ)
    (hA : ∀ a, (grs k hk f hf).Afun F ρ a ≠ 0)
    (α β : AdjoinRoot f) (hα : (grs k hk f hf).π α = ρ) :
    GRS.delta F α β = GRS.delta (F.map (psiGR k hk f)) (psiGR k hk f α) (psiGR k hk f β) := by
  obtain ⟨hc, _⟩ := grs_card k hk f hf
  exact GRS.delta_stable_mod8 (compatGR k hk f hf) (card_GR8 k hk f hf) hc F ρ μ H hA α β hα

end GR

end APN2
