import Apn2R03.Inter4
import Apn2R03.Family5b

/-!
# Corollary interfamily: `F♯` for `r ≥ 5` is optimal on every lower layer (Claude, 2026-10-26, R05c)

* `choose3_cast_zero`, `p5_hasse3` : `F̄^[3] = 0` for the family (no monomial `X^3`, `c₃ = 0`);
* `p5_hasse2_ne`                   : `p^[2] = 1 + X^w + X^u` has no zero (`Tr p^[2] = 1`);
* `fam5_hd2`                       : `p'` is two-to-one on the pairs `{a, a+1}`;
* `fam5_interfamily`               : for every `k ≥ 3`, every `1 ≤ j ≤ k−2` and every unit `u`, every entry of the
                                     row of `2^j u` of `F♯ = Fsh5` is `0` or `q^(j+1)`.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

section field
variable {K : Type*} [Field K] [CharP K 2]

theorem choose3_cast_zero (n : ℕ) (hn : n % 4 ≠ 3) : ((n.choose 3 : ℕ) : K) = 0 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · rw [Nat.choose_eq_zero_of_lt h]; simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hd : (m + 3).descFactorial 3 = Nat.factorial 3 * (m + 3).choose 3 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hd' : (m + 3).descFactorial 3 = (m + 3) * (m + 2) * (m + 1) := by
    simp [Nat.descFactorial]; ring
  have hmod : ((m + 3) * (m + 2) * (m + 1)) % 4 = 0 := by
    have : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases this with h | h | h <;> simp [Nat.mul_mod, Nat.add_mod, h]
  have hev : (m + 3).choose 3 % 2 = 0 := by
    have : (6 * (m + 3).choose 3) % 4 = 0 := by
      rw [← hmod, ← hd', hd]; rfl
    omega
  obtain ⟨t, ht⟩ : ∃ t, (m + 3).choose 3 = 2 * t := ⟨(m + 3).choose 3 / 2, by omega⟩
  rw [ht]; push_cast; rw [two_K]; ring

theorem h3_eval (n : ℕ) (x : K) :
    (hasseDeriv 3 ((X : K[X]) ^ n)).eval x = ((n.choose 3 : ℕ) : K) * x ^ (n - 3) := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  simp only [eval_monomial, mul_one]

theorem h3_zero (n : ℕ) (hn : n % 4 ≠ 3) (x : K) : (hasseDeriv 3 ((X : K[X]) ^ n)).eval x = 0 := by
  rw [h3_eval, choose3_cast_zero n hn, zero_mul]

theorem h3_4k (k : ℕ) (x : K) : (hasseDeriv 3 ((X : K[X]) ^ (4 * k))).eval x = 0 :=
  h3_zero _ (by omega) x

theorem h3_4k1 (k : ℕ) (x : K) : (hasseDeriv 3 ((X : K[X]) ^ (4 * k + 1))).eval x = 0 :=
  h3_zero _ (by omega) x

theorem h3_4k2 (k : ℕ) (x : K) : (hasseDeriv 3 ((X : K[X]) ^ (4 * k + 2))).eval x = 0 :=
  h3_zero _ (by omega) x

/-- `c₃ = 0` for the family `r ≥ 5` -/
theorem p5_hasse3 (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) (x : K) :
    (hasseDeriv 3 (F5 K m r)).eval x = 0 := by
  have ew : 2 ^ (r - 2) = 4 * 2 ^ (r - 4) := by
    rw [show r - 2 = (r - 4) + 2 by omega, pow_add]; ring
  have eu : 2 ^ (m - 2) = 4 * 2 ^ (m - 4) := by
    rw [show m - 2 = (m - 4) + 2 by omega, pow_add]; ring
  have ev : 2 ^ (m - 1) = 4 * 2 ^ (m - 3) := by
    rw [show m - 1 = (m - 3) + 2 by omega, pow_add]; ring
  have hz : (hasseDeriv 3 (Z5 K m r)).eval x = 0 := by
    unfold Z5
    rw [map_sum, eval_finsetSum]
    apply sum_eq_zero
    intro i _
    have ei : 2 ^ (i + 2) = 4 * 2 ^ i := by rw [pow_add]; ring
    rw [map_add, map_add, eval_add, eval_add, ei, ew, eu, ← mul_add, ← mul_add, h3_4k, h3_4k, h3_4k]
    ring
  unfold F5
  simp only [map_add, eval_add]
  rw [hz]
  have hX1 : (hasseDeriv 3 (X : K[X])).eval x = 0 := by
    have := h3_zero (K := K) 1 (by norm_num) x; simpa using this
  have hX2 : (hasseDeriv 3 ((X : K[X]) ^ 2)).eval x = 0 := h3_zero 2 (by norm_num) x
  rw [hX1, hX2, ew, eu, ev, h3_4k, h3_4k1, h3_4k2, ← mul_add, h3_4k, ← mul_add, h3_4k, h3_4k1,
    h3_4k2, ← mul_add, h3_4k]
  ring

/-- `p^[2] = 1 + x^w + x^u` has no zero -/
theorem p5_hasse2_ne [Fintype K] (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) (hodd : Odd m)
    (hcard : Fintype.card K = 2 ^ m) (x : K) : (hasseDeriv 2 (F5 K m r)).eval x ≠ 0 := by
  rw [p5_hasse2 m r hm hr x]
  intro h
  have := congrArg (absTr m) h
  rw [absTr_add, absTr_add, absTr_one m hodd, absTr_pow_two_pow m hcard x,
    absTr_pow_two_pow m hcard x, absTr_zero] at this
  have h2 : (2 : K) = 0 := two_K
  have : (1 : K) = 0 := by linear_combination this - absTr m x * h2
  exact one_ne_zero this

theorem p5_hd2 [Fintype K] (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (a b : K)
    (h : (F5 K m r).derivative.eval a = (F5 K m r).derivative.eval b) : b = a ∨ b = a + 1 := by
  have h2 : (2 : K) = 0 := two_K
  have hab : (F5 K m r).derivative.eval (a + b) = (F5 K m r).derivative.eval 0 := by
    rw [p5_deriv_add m r (by omega) (by omega), h]
    linear_combination ((F5 K m r).derivative.eval b - (F5 K m r).derivative.eval 0) * h2
  rcases (p5_ker m r hm5 hr5 hrm hcard hcop (a + b)).mp hab with h0 | h1
  · left; linear_combination h0 - a * h2
  · right; linear_combination h1 - a * h2

end field

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- a value that is never attained has an empty row entry -/
theorem delta_zero_of_not (f : R[X]) (α β : R) (h : ∀ x0, β ≠ f.eval (x0 + α) - f.eval x0) :
    delta f α β = 0 := by
  unfold delta
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  exact h x hx.symm

/-- **Corollary interfamily.** For `r ≥ 5`, every entry of every row of every lower layer `v_j`
(`1 ≤ j ≤ k−2`) of `F♯` is `0` or `q^(j+1)`. -/
theorem fam5_interfamily (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (j : ℕ) (hj : 1 ≤ j) (hjk : j + 2 ≤ S.k) (u β : R) (hu : S.π u ≠ 0) :
    delta (Fsh5 R m r) (2 ^ j * u) β = 0 ∨
      delta (Fsh5 R m r) (2 ^ j * u) β = Fintype.card K ^ (j + 1) := by
  haveI := S.charP2
  have H := S.fam5_sh_hyp m r hm5 hr5 hrm hodd hm hcop
  have hmap := S.fam5_sh_map (R := R) m r
  have hd2 : ∀ a b : K, ((Fsh5 R m r).map S.π).derivative.eval a =
      ((Fsh5 R m r).map S.π).derivative.eval b → b = a ∨ b = a + 1 := by
    rw [hmap]; exact p5_hd2 m r hm5 hr5 hrm hm hcop
  have hA : ∀ a, S.Afun (Fsh5 R m r) 1 a ≠ 0 := by
    intro a; rw [S.fam5_sh_A m r hm5 hr5 hrm hodd hm hcop]; exact A5s_ne m r hmodd hm a
  rcases Nat.lt_or_ge (j + 2) S.k with hlt | hge
  · -- 1 ≤ j ≤ k − 3: Theorem inter
    have hc3 : ∀ a, (hasseDeriv 3 ((Fsh5 R m r).map S.π)).eval a = 0 := by
      rw [hmap]; exact p5_hasse3 m r hm5 hr5
    have hp2 : ∀ a, (hasseDeriv 2 ((Fsh5 R m r).map S.π)).eval a ≠ 0 := by
      rw [hmap]; exact p5_hasse2_ne m r hm5 hr5 hmodd hm
    have hup := (S.inter_upper hcard (Fsh5 R m r) 1 0 H hd2 j hj (by omega) u hu hc3 hp2 β).2
      (fun a => by rw [mul_zero, add_zero]; exact hA a)
    obtain ⟨t, ht⟩ := S.inter_dvd hcard (Fsh5 R m r) j hj hjk u β
    have hq : 0 < Fintype.card K ^ (j + 1) := pow_pos Fintype.card_pos _
    rw [ht] at hup ⊢
    have : t ≤ 1 := by
      by_contra ht1; push Not at ht1
      have := Nat.mul_lt_mul_of_pos_left ht1 hq
      omega
    interval_cases t <;> simp
  · have hjk' : j = S.k - 2 := by omega
    by_cases hatt : ∃ x0, β = (Fsh5 R m r).eval (x0 + 2 ^ j * u) - (Fsh5 R m r).eval x0
    · obtain ⟨x0, rfl⟩ := hatt
      right
      rcases Nat.lt_or_ge 3 S.k with hk | hk
      · -- penultimate layer, k ≥ 4
        have h := S.penultimate hcard (by omega) (Fsh5 R m r) 1 0 H hd2 u x0 hu
        rw [← hjk'] at h
        rw [h, if_neg (hA _), mul_one, show S.k - 1 = j + 1 by omega]
      · -- k = 3, j = 1: the middle layer
        have hk3 : S.k = 3 := by have := S.hk; omega
        have hj1 : j = 1 := by omega
        subst hj1
        have h := S.middle_k3 hk3 hcard (Fsh5 R m r) 1 0 H hd2 u x0 hu
        rw [pow_one, h, if_neg, mul_one]
        rw [mul_zero, add_zero]
        exact mul_ne_zero hu (hA _)
    · left
      apply delta_zero_of_not
      intro x0 hx0
      exact hatt ⟨x0, hx0⟩

end GRS

end APN2

#print axioms APN2.p5_hasse3
#print axioms APN2.GRS.fam5_interfamily
