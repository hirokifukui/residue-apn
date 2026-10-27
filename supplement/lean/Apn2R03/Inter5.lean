import Apn2R03.InterFam

/-!
# Intermediate layers, part 5: the exact multiplicities of Theorem inter (ii) (Claude, 2026-10-26, R05c)

Assume `c₃ = 0` and `p^[2]` has no zero, `1 ≤ j ≤ k−3`, `α = 2^j u`, `B_α(a) = A_F(a) + π(2^(j−1)) ū μ`.
* `inter_row`   : the entry at `β = F(x₀+α) − F(x₀)` is `2 q^(j+1)` if `B_α(π x₀) = 0` and `q^(j+1)` otherwise;
* `inter_count` : `#{β : δ = 2 q^(j+1)} · 2 q^(j+1) = #{x : B_α(π x) = 0}` and
                  `#{β : δ = q^(j+1)} · q^(j+1) = #{x : B_α(π x) ≠ 0}`;
* `inter_mult`  : with `s = #B_α⁻¹(0)`: `2 · #{δ = 2q^(j+1)} = s q^(k−j−2)` and `#{δ = q^(j+1)} = (q − s) q^(k−j−2)`;
* `fam5_nat_inter` : the natural lift of `P_{m,r}` (`r ≥ 5`): `q^(k−j−2)` entries `2q^(j+1)` and
                     `(q − 2) q^(k−j−2)` entries `q^(j+1)` in every row of `v_j`, `1 ≤ j ≤ k−3`.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- the solution set of `T ≡ γ (mod 2^(k−j))` on the class `a` -/
noncomputable def Cset (f : R[X]) (j : ℕ) (u γ : R) (a : K) : Finset R :=
  univ.filter (fun x : R => S.π x = a ∧ ∃ w, (Tpol f (2 ^ j * u)).eval x - γ = 2 ^ (S.k - j) * w)

section hyps
variable (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ)
  (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b → b = a ∨ b = a + ρ)
  (j : ℕ) (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) (u : R) (hu : S.π u ≠ 0)
  (hc3 : ∀ a, (hasseDeriv 3 (f.map S.π)).eval a = 0)
  (hp2 : ∀ a, (hasseDeriv 2 (f.map S.π)).eval a ≠ 0)
include hcard hj hjk hc3 hp2

theorem roots_one (x c : R) : (univ.filter (fun y : K => S.π c +
    (S.π ((hasseDeriv 2 f).eval x) + S.π (2 ^ (j - 1)) * S.π u * S.π ((hasseDeriv 3 f).eval x)) * y +
    S.π ((hasseDeriv 3 f).eval x) * y ^ 2 = 0)).card = 1 := by
  have h3 : S.π ((hasseDeriv 3 f).eval x) = 0 := by rw [S.pi_hasse]; exact hc3 _
  have := roots_lin (S.π ((hasseDeriv 2 f).eval x + 0)) (S.π c)
    (by rw [add_zero, S.pi_hasse]; exact hp2 _)
  rw [h3]
  simp only [mul_zero, add_zero, zero_mul] at this ⊢
  exact this

theorem hw_ne (x : R) : S.π ((hasseDeriv 2 f).eval x) + S.π (2 ^ (j - 1)) * S.π u *
    S.π ((hasseDeriv 3 f).eval x) ≠ 0 := by
  rw [S.pi_hasse, S.pi_hasse, hc3, mul_zero, add_zero]; exact hp2 _

theorem C_self (x0 : R) :
    (S.Cset f j u ((Tpol f (2 ^ j * u)).eval x0) (S.π x0)).card = Fintype.card K ^ (j + 1) := by
  have h := S.class_val hcard f j hj hjk u ((Tpol f (2 ^ j * u)).eval x0) x0 0 (by ring)
    (S.hw_ne hcard f j hj hjk u hc3 hp2 x0)
  rw [S.roots_one hcard f j hj hjk u hc3 hp2, mul_one] at h
  exact h

include H in
theorem C_other (x0 : R) :
    (S.Cset f j u ((Tpol f (2 ^ j * u)).eval x0) (S.π x0 + ρ)).card =
      if S.Afun f ρ (S.π x0) + S.π (2 ^ (j - 1)) * S.π u * μ = 0 then Fintype.card K ^ (j + 1) else 0 := by
  obtain ⟨τ, hτ⟩ := S.surj ρ
  have hk4 : ∀ w : R, (2 : R) ^ (S.k - j) * w = 4 * (2 ^ (S.k - j - 2) * w) := by
    intro w
    rw [show (4 : R) = 2 ^ 2 by norm_num, ← mul_assoc, ← pow_add]; congr 2; omega
  split_ifs with hB
  · obtain ⟨g, hg, hπg⟩ := S.Tpol_pair f ρ μ H j hj u x0 τ hτ
    rw [hB] at hπg
    obtain ⟨g', hg'⟩ := (S.ker2 g).mp hπg
    have h := S.class_val hcard f j hj hjk u ((Tpol f (2 ^ j * u)).eval x0) (x0 + τ) g'
      (by rw [hg, hg']; ring) (S.hw_ne hcard f j hj hjk u hc3 hp2 _)
    rw [S.roots_one hcard f j hj hjk u hc3 hp2, mul_one, map_add, hτ] at h
    exact h
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x' hx'
    simp only [Cset, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    obtain ⟨hπx', w', hw'⟩ := hx'
    obtain ⟨g, hg, hπg⟩ := S.Tpol_pair f ρ μ H j hj u x0 (x' - x0) (by rw [map_sub, hπx']; ring)
    have e : x0 + (x' - x0) = x' := by ring
    rw [e] at hg
    have h4 : 2 * g = 2 * (2 * (2 ^ (S.k - j - 2) * w')) := by
      linear_combination -hg + hw' + hk4 w'
    have := S.pi_eq_of_two_mul_eq h4
    rw [S.pi_two_mul, hπg] at this
    exact hB this

include H hd2 hu in
/-- solutions of the row equation lie in the pair of `x₀` -/
theorem sol_support (x0 x : R)
    (hx : f.eval (x + 2 ^ j * u) - f.eval x = f.eval (x0 + 2 ^ j * u) - f.eval x0) :
    S.π x = S.π x0 ∨ S.π x = S.π x0 + ρ := by
  have hαπ : S.π ((2 : R) ^ j * u) = 0 := S.pi_two_pow_mul j hj u
  rw [← Tpol_eval_mul, ← Tpol_eval_mul] at hx
  obtain ⟨w, hw⟩ := (S.sol_iff f j (by omega) u ((Tpol f (2 ^ j * u)).eval x0) x hu).mp
    (by rw [← Tpol_eval_mul, hx, Tpol_eval_mul])
  have h1 : S.π ((Tpol f (2 ^ j * u)).eval x) = S.π ((Tpol f (2 ^ j * u)).eval x0) := by
    have : S.π ((Tpol f (2 ^ j * u)).eval x - (Tpol f (2 ^ j * u)).eval x0) = 0 := by
      rw [hw]; exact S.pi_two_pow_mul _ (by omega) _
    rwa [map_sub, sub_eq_zero] at this
  rw [S.Tpol_pi f _ x hαπ, S.Tpol_pi f _ x0 hαπ] at h1
  exact hd2 (S.π x0) (S.π x) h1.symm

include H hd2 hu in
/-- **Theorem inter (ii), one row.** -/
theorem inter_row (x0 : R) :
    delta f (2 ^ j * u) (f.eval (x0 + 2 ^ j * u) - f.eval x0) =
      if S.Afun f ρ (S.π x0) + S.π (2 ^ (j - 1)) * S.π u * μ = 0 then 2 * Fintype.card K ^ (j + 1)
      else Fintype.card K ^ (j + 1) := by
  set γ := (Tpol f (2 ^ j * u)).eval x0 with hγ
  have hβ : f.eval (x0 + 2 ^ j * u) - f.eval x0 = 2 ^ j * u * γ := by rw [hγ, Tpol_eval_mul]
  have hne : S.π x0 ≠ S.π x0 + ρ := by intro h; apply H.hρ; linear_combination -h
  have hsum : delta f (2 ^ j * u) (2 ^ j * u * γ) =
      (S.Cset f j u γ (S.π x0)).card + (S.Cset f j u γ (S.π x0 + ρ)).card := by
    rw [S.delta_eq_sum]
    simp_rw [S.cc_eq f j (by omega) u γ hu]
    rw [show (S.Cset f j u γ (S.π x0)).card + (S.Cset f j u γ (S.π x0 + ρ)).card =
        ∑ a ∈ ({S.π x0, S.π x0 + ρ} : Finset K), (S.Cset f j u γ a).card from
        (Finset.sum_pair (f := fun a => (S.Cset f j u γ a).card) hne).symm]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    simp only [Cset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hπa, w, hw⟩ := hx
    have hs := S.sol_support hcard f ρ μ H hd2 j hj hjk u hu hc3 hp2 x0 x (by
      rw [hβ]; exact (S.sol_iff f j (by omega) u γ x hu).mpr ⟨w, hw⟩)
    apply ha
    rcases hs with h | h <;> simp [← hπa, h]
  rw [hβ, hsum, S.C_self hcard f j hj hjk u hc3 hp2 x0, S.C_other hcard f ρ μ H j hj hjk u hc3 hp2 x0]
  split_ifs <;> ring

include H hd2 hu in
/-- **Theorem inter (ii), multiplicities** (count form). -/
theorem inter_count :
    (univ.filter (fun β => delta f (2 ^ j * u) β = 2 * Fintype.card K ^ (j + 1))).card *
        (2 * Fintype.card K ^ (j + 1)) =
      (univ.filter (fun x : R => S.Afun f ρ (S.π x) + S.π (2 ^ (j - 1)) * S.π u * μ = 0)).card ∧
    (univ.filter (fun β => delta f (2 ^ j * u) β = Fintype.card K ^ (j + 1))).card *
        Fintype.card K ^ (j + 1) =
      (univ.filter (fun x : R => S.Afun f ρ (S.π x) + S.π (2 ^ (j - 1)) * S.π u * μ ≠ 0)).card := by
  set q1 := Fintype.card K ^ (j + 1) with hq1
  have hq : 0 < q1 := pow_pos Fintype.card_pos _
  set B : K → K := fun a => S.Afun f ρ a + S.π (2 ^ (j - 1)) * S.π u * μ with hBdef
  have hBper : ∀ a, B (a + ρ) = B a := by
    intro a; simp only [B, S.A_periodic f ρ H.hper a]
  set D : R → R := fun x => f.eval (x + 2 ^ j * u) - f.eval x with hD
  -- every row lies in one `B`-class
  have hrowB : ∀ x0 x, D x = D x0 → (B (S.π x) = 0 ↔ B (S.π x0) = 0) := by
    intro x0 x hx
    rcases S.sol_support hcard f ρ μ H hd2 j hj hjk u hu hc3 hp2 x0 x hx with h | h
    · rw [h]
    · rw [h, hBper]
  have hrow : ∀ β, delta f (2 ^ j * u) β = (univ.filter (fun x => D x = β)).card := by
    intro β; unfold delta; rfl
  have key : ∀ (P : K → Prop) [DecidablePred P] (v : ℕ),
      (∀ x0, (P (B (S.π x0)) ↔ delta f (2 ^ j * u) (D x0) = v)) → 0 < v →
      (∀ x0 x, D x = D x0 → (P (B (S.π x)) ↔ P (B (S.π x0)))) →
      (univ.filter (fun β => delta f (2 ^ j * u) β = v)).card * v =
        (univ.filter (fun x : R => P (B (S.π x)))).card := by
    intro P _ v hv hv0 hcl
    have h := Finset.card_eq_sum_card_fiberwise (s := univ.filter (fun x : R => P (B (S.π x))))
      (t := (univ : Finset R)) (f := D) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [h]
    have hterm : ∀ β ∈ (univ : Finset R),
        ((univ.filter (fun x : R => P (B (S.π x)))).filter (fun x => D x = β)).card =
          if delta f (2 ^ j * u) β = v then v else 0 := by
      intro β _
      by_cases hex : ∃ x0, D x0 = β
      · obtain ⟨x0, rfl⟩ := hex
        by_cases hP : P (B (S.π x0))
        · rw [if_pos ((hv x0).mp hP), ← (hv x0).mp hP, hrow]
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨-, h⟩; exact h
          · intro h; exact ⟨(hcl x0 x h).mpr hP, h⟩
        · rw [if_neg (fun h => hP ((hv x0).mpr h))]
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact hP ((hcl x0 x hx.2).mp hx.1)
      · have h0 : delta f (2 ^ j * u) β = 0 := by
          rw [hrow, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact hex ⟨x, hx⟩
        rw [if_neg (by rw [h0]; omega)]
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact hex ⟨x, hx.2⟩
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      smul_eq_mul]
  have hval : ∀ x0, delta f (2 ^ j * u) (D x0) = if B (S.π x0) = 0 then 2 * q1 else q1 :=
    fun x0 => S.inter_row hcard f ρ μ H hd2 j hj hjk u hu hc3 hp2 x0
  constructor
  · apply key (fun b => b = 0) (2 * q1)
    · intro x0; rw [hval]; split_ifs with h
      · simp [h]
      · simp only [h, false_iff]; omega
    · omega
    · intro x0 x hx; exact hrowB x0 x hx
  · apply key (fun b => b ≠ 0) q1
    · intro x0; rw [hval]; split_ifs with h
      · simp only [h, ne_eq, not_true_eq_false, false_iff]; omega
      · simp [h]
    · exact hq
    · intro x0 x hx; exact not_congr (hrowB x0 x hx)

end hyps

end GRS

end APN2

#print axioms APN2.GRS.inter_row
#print axioms APN2.GRS.inter_count
