import Apn2R03.Inter5
import Apn2R03.Natural

/-!
# Intermediate layers, part 6: multiplicities in closed form, natural lift (Claude, 2026-10-26, R05c)
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem card_pred_pi (hcard : Fintype.card R = Fintype.card K ^ S.k) (P : K → Prop) [DecidablePred P] :
    (univ.filter (fun x : R => P (S.π x))).card = (univ.filter P).card * Fintype.card K ^ (S.k - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : R => S.π x) (t := univ.filter P)
    (fun x hx => Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2⟩))]
  rw [← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  rw [← S.card_fiber hcard a]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨by rw [h]; exact ha, h⟩

/-- **Theorem inter (ii)**: with `s = #B_α⁻¹(0)` and `d = k − j − 2`, the row of `α` has
`s/2 · q^d` entries `2 q^(j+1)` and `(q − s) q^d` entries `q^(j+1)`. -/
theorem inter_mult (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b → b = a ∨ b = a + ρ)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) (u : R) (hu : S.π u ≠ 0)
    (hc3 : ∀ a, (hasseDeriv 3 (f.map S.π)).eval a = 0)
    (hp2 : ∀ a, (hasseDeriv 2 (f.map S.π)).eval a ≠ 0) :
    2 * (univ.filter (fun β => delta f (2 ^ j * u) β = 2 * Fintype.card K ^ (j + 1))).card =
        (univ.filter (fun a : K => S.Afun f ρ a + S.π (2 ^ (j - 1)) * S.π u * μ = 0)).card *
          Fintype.card K ^ (S.k - j - 2) ∧
      (univ.filter (fun β => delta f (2 ^ j * u) β = Fintype.card K ^ (j + 1))).card =
        (univ.filter (fun a : K => S.Afun f ρ a + S.π (2 ^ (j - 1)) * S.π u * μ ≠ 0)).card *
          Fintype.card K ^ (S.k - j - 2) := by
  obtain ⟨h2, h1⟩ := S.inter_count hcard f ρ μ H hd2 j hj hjk u hu hc3 hp2
  rw [S.card_pred_pi hcard (fun b => S.Afun f ρ b + S.π (2 ^ (j - 1)) * S.π u * μ = 0)] at h2
  rw [S.card_pred_pi hcard (fun b => S.Afun f ρ b + S.π (2 ^ (j - 1)) * S.π u * μ ≠ 0)] at h1
  have hq : 0 < Fintype.card K ^ (j + 1) := pow_pos Fintype.card_pos _
  have e : Fintype.card K ^ (S.k - 1) = Fintype.card K ^ (S.k - j - 2) * Fintype.card K ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e] at h1 h2
  set N2 := (univ.filter (fun β => delta f (2 ^ j * u) β = 2 * Fintype.card K ^ (j + 1))).card
  set N1 := (univ.filter (fun β => delta f (2 ^ j * u) β = Fintype.card K ^ (j + 1))).card
  set s2 := (univ.filter (fun a : K => S.Afun f ρ a + S.π (2 ^ (j - 1)) * S.π u * μ = 0)).card
  set s1 := (univ.filter (fun a : K => S.Afun f ρ a + S.π (2 ^ (j - 1)) * S.π u * μ ≠ 0)).card
  set qd := Fintype.card K ^ (S.k - j - 2)
  set q1 := Fintype.card K ^ (j + 1)
  constructor
  · apply Nat.eq_of_mul_eq_mul_right hq
    calc 2 * N2 * q1 = N2 * (2 * q1) := by ring
      _ = s2 * (qd * q1) := h2
      _ = s2 * qd * q1 := by ring
  · apply Nat.eq_of_mul_eq_mul_right hq
    calc N1 * q1 = s1 * (qd * q1) := h1
      _ = s1 * qd * q1 := by ring

/-- **Corollary interfamily, natural lift.** For the natural lift of `P_{m,r}` (`r ≥ 5`) and `1 ≤ j ≤ k−3`,
every row of `v_j` has `q^(k−j−2)` entries `2 q^(j+1)` and `(q − 2) q^(k−j−2)` entries `q^(j+1)`. -/
theorem fam5_nat_inter (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (j : ℕ) (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) (u : R) (hu : S.π u ≠ 0) :
    (univ.filter (fun β => delta (F5 R m r) (2 ^ j * u) β = 2 * Fintype.card K ^ (j + 1))).card =
        Fintype.card K ^ (S.k - j - 2) ∧
      (univ.filter (fun β => delta (F5 R m r) (2 ^ j * u) β = Fintype.card K ^ (j + 1))).card =
        (Fintype.card K - 2) * Fintype.card K ^ (S.k - j - 2) := by
  haveI := S.charP2
  obtain ⟨H, hd2⟩ := S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop
  have hmap : (F5 R m r).map S.π = F5 K m r := F5_map S.π m r
  have hc3 : ∀ a, (hasseDeriv 3 ((F5 R m r).map S.π)).eval a = 0 := by
    rw [hmap]; exact p5_hasse3 m r hm5 hr5
  have hp2 : ∀ a, (hasseDeriv 2 ((F5 R m r).map S.π)).eval a ≠ 0 := by
    rw [hmap]; exact p5_hasse2_ne m r hm5 hr5 hmodd hm
  obtain ⟨e2, e1⟩ := S.inter_mult hcard (F5 R m r) 1 0 H hd2 j hj hjk u hu hc3 hp2
  have hZ : univ.filter (fun a : K => S.Afun (F5 R m r) 1 a + S.π (2 ^ (j - 1)) * S.π u * 0 = 0) =
      ({0, 1} : Finset K) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_zero, add_zero, Finset.mem_insert,
      Finset.mem_singleton]
    rw [S.fam5_A m r hm5 hr5 hrm hodd hm hcop]
    constructor
    · exact A5n_zero m r hm5 hr5 hmodd hm hcop a
    · have h0 := S.fam5_nat_A0 (R := R) m r hm5 hr5 hrm hodd hm hcop
      rw [S.fam5_A m r hm5 hr5 hrm hodd hm hcop] at h0
      rintro (rfl | rfl)
      · exact h0
      · have hper := S.A_periodic (F5 R m r) 1 H.hper 0
        rw [zero_add, S.fam5_A m r hm5 hr5 hrm hodd hm hcop, S.fam5_A m r hm5 hr5 hrm hodd hm hcop] at hper
        rw [hper]; exact h0
  have hZc : (univ.filter (fun a : K => ¬ (S.Afun (F5 R m r) 1 a + S.π (2 ^ (j - 1)) * S.π u * 0 = 0))).card =
      Fintype.card K - 2 := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset K))
      (fun a : K => S.Afun (F5 R m r) 1 a + S.π (2 ^ (j - 1)) * S.π u * 0 = 0)
    rw [hZ, Finset.card_pair zero_ne_one, Finset.card_univ] at this
    omega
  simp only [ne_eq] at e1
  rw [hZ, Finset.card_pair zero_ne_one] at e2
  rw [hZc] at e1
  exact ⟨by omega, e1⟩


/-- **Theorem inter (iii)** for the whole layer `v_j` (`1 ≤ j ≤ k−3`, all unit `u`). -/
theorem inter_layer_iff (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b → b = a ∨ b = a + ρ)
    (hred : (f.map S.π).natDegree < Fintype.card K) (c3 : K) (hc3 : hasseDeriv 3 (f.map S.π) = C c3)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) :
    (∀ u β : R, S.π u ≠ 0 →
        delta f (2 ^ j * u) β = 0 ∨ delta f (2 ^ j * u) β = Fintype.card K ^ (j + 1)) ↔
      (c3 = 0 ∧ (∀ a, (hasseDeriv 2 (f.map S.π)).eval a ≠ 0) ∧
        (if j = 1 ∧ μ ≠ 0 then ∀ a, S.Afun f ρ a = 0 else ∀ a, S.Afun f ρ a ≠ 0)) := by
  have h2 := S.two_F
  have key : ∀ u : R, S.π u ≠ 0 →
      ((∀ β, delta f (2 ^ j * u) β = 0 ∨ delta f (2 ^ j * u) β = Fintype.card K ^ (j + 1)) ↔
        (c3 = 0 ∧ (∀ a, (hasseDeriv 2 (f.map S.π)).eval a ≠ 0) ∧
          ∀ a, S.Afun f ρ a + S.π (2 ^ (j - 1)) * S.π u * μ ≠ 0)) :=
    fun u hu => S.inter_flat_iff hcard f ρ μ H hd2 hred c3 hc3 j hj hjk u hu
  obtain ⟨u1, hu1⟩ := S.surj 1
  have hu1' : S.π u1 ≠ 0 := by rw [hu1]; exact one_ne_zero
  by_cases hcase : j = 1 ∧ μ ≠ 0
  · obtain ⟨rfl, hμ⟩ := hcase
    rw [if_pos ⟨rfl, hμ⟩]
    constructor
    · intro hall
      obtain ⟨h3, hp, -⟩ := (key u1 hu1').mp (fun β => hall u1 β hu1')
      refine ⟨h3, hp, fun a => ?_⟩
      by_contra hA
      obtain ⟨v, hv⟩ := S.surj (S.Afun f ρ a / μ)
      have hv0 : S.π v ≠ 0 := by rw [hv]; exact div_ne_zero hA hμ
      obtain ⟨-, -, hB⟩ := (key v hv0).mp (fun β => hall v β hv0)
      apply hB a
      rw [S.pi_two_pow_pred 1 le_rfl, if_pos rfl, one_mul, hv]
      field_simp
      linear_combination S.Afun f ρ a * h2
    · rintro ⟨h3, hp, hA⟩ u β hu
      refine (key u hu).mpr ⟨h3, hp, fun a => ?_⟩ β
      rw [S.pi_two_pow_pred 1 le_rfl, if_pos rfl, one_mul, hA a, zero_add]
      exact mul_ne_zero hu hμ
  · rw [if_neg hcase]
    have hB0 : ∀ u : R, S.π (2 ^ (j - 1)) * S.π u * μ = 0 := by
      intro u
      rw [S.pi_two_pow_pred j hj]
      by_cases hj1 : j = 1
      · have hμ : μ = 0 := by by_contra h; exact hcase ⟨hj1, h⟩
        rw [hμ, mul_zero]
      · rw [if_neg hj1, zero_mul, zero_mul]
    constructor
    · intro hall
      obtain ⟨h3, hp, hB⟩ := (key u1 hu1').mp (fun β => hall u1 β hu1')
      refine ⟨h3, hp, fun a => ?_⟩
      have := hB a
      rwa [hB0, add_zero] at this
    · rintro ⟨h3, hp, hA⟩ u β hu
      refine (key u hu).mpr ⟨h3, hp, fun a => ?_⟩ β
      rw [hB0, add_zero]; exact hA a

end GRS

end APN2

#print axioms APN2.GRS.inter_mult
#print axioms APN2.GRS.fam5_nat_inter
#print axioms APN2.GRS.inter_layer_iff
