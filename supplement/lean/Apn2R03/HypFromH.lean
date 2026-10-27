import Apn2R03.Bounds

/-!
# From the paper's hypothesis (H) to `Hyp` (FOUNDATIONS F0) (Claude, 2026-10-25)

(H) for p = f mod 2:
* `IsQuadSupport p` : every exponent of p is 0, 2^i or 2^i + 2^j (i < j)   (p quadratic);
* `hker` : p'(x) = p'(0) ⟺ x ∈ {0, ρ}, with ρ ≠ 0       (p' = ε + K, ker K = {0, ρ});
* `hapn` : #{x : p(x+ρ) − p(x) = b} ≤ 2 for every b       (APN in direction ρ).
Then `Hyp f ρ μ` holds with μ = p^[2](ρ) − p^[2](0), and p'(a) = p'(b) ⇒ b ∈ {a, a+ρ}.
The key facts are that p' and p^[2] are affine for quadratic p (Lucas' theorem for C(e,2) mod 2).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

section field
variable {K : Type*} [Field K] [CharP K 2]

def IsQuadSupport (p : K[X]) : Prop :=
  ∀ e ∈ p.support, e = 0 ∨ (∃ i, e = 2 ^ i) ∨ (∃ i j, i < j ∧ e = 2 ^ i + 2 ^ j)

def IsAffine (g : K → K) : Prop := ∀ x y, g (x + y) = g x + g y - g 0

theorem two_K : (2 : K) = 0 := CharTwo.two_eq_zero

theorem natCast_two_pow (i : ℕ) (hi : 1 ≤ i) : ((2 ^ i : ℕ) : K) = 0 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, two_K, zero_pow (by omega)]

theorem frob_add (j : ℕ) (x y : K) : (x + y) ^ (2 ^ j) = x ^ (2 ^ j) + y ^ (2 ^ j) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [add_pow_char_pow]

theorem choose2_cast (n : ℕ) : ((n.choose 2 : ℕ) : K) = ((n / 2 : ℕ) : K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 2) (p := 2)
  simp only [Nat.mod_self, Nat.choose_zero_right, one_mul, Nat.div_self (by norm_num : 0 < 2),
    Nat.choose_one_right] at h
  exact (CharP.natCast_eq_natCast K 2).mpr h

theorem affine_sum (s : Finset ℕ) (t : ℕ → K → K) (h : ∀ e ∈ s, IsAffine (t e)) :
    IsAffine (fun x => ∑ e ∈ s, t e x) := by
  intro x y
  simp only
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun e he => h e he x y)

theorem affine_const (c : K) : IsAffine (fun _ : K => c) := by intro x y; ring
theorem affine_zero : IsAffine (fun _ : K => (0 : K)) := by intro x y; ring
theorem affine_frob (c : K) (j : ℕ) : IsAffine (fun x : K => c * x ^ (2 ^ j)) := by
  intro x y
  simp only
  rw [frob_add, zero_pow (by positivity)]; ring

theorem deriv_eval_sum (p : K[X]) (x : K) :
    p.derivative.eval x = ∑ e ∈ p.support, p.coeff e * (e : K) * x ^ (e - 1) := by
  rw [derivative_apply, Polynomial.sum_def, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro e _
  simp [eval_mul, eval_C, eval_pow, eval_X]

theorem hasse2_eval_sum (p : K[X]) (x : K) :
    (hasseDeriv 2 p).eval x = ∑ e ∈ p.support, ((e.choose 2 : ℕ) : K) * p.coeff e * x ^ (e - 2) := by
  rw [hasseDeriv_apply, Polynomial.sum_def, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro e _
  simp [eval_monomial]

theorem term_deriv_affine (e : ℕ)
    (he : e = 0 ∨ (∃ i, e = 2 ^ i) ∨ (∃ i j, i < j ∧ e = 2 ^ i + 2 ^ j)) (c : K) :
    IsAffine (fun x : K => c * (e : K) * x ^ (e - 1)) := by
  rcases he with rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · simpa using affine_zero
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa using affine_const c
    · have : ((2 ^ i : ℕ) : K) = 0 := natCast_two_pow i hi
      simp only [Nat.cast_pow, Nat.cast_ofNat] at this
      simp only [Nat.cast_pow, Nat.cast_ofNat, this, mul_zero, zero_mul]
      exact affine_zero
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hj : 1 ≤ j := by omega
      have h1 : ((2 ^ 0 + 2 ^ j : ℕ) : K) = 1 := by
        rw [Nat.cast_add, natCast_two_pow j hj]; simp
      have h2 : 2 ^ 0 + 2 ^ j - 1 = 2 ^ j := by simp
      rw [show (fun x : K => c * ((2 ^ 0 + 2 ^ j : ℕ) : K) * x ^ (2 ^ 0 + 2 ^ j - 1)) =
        fun x : K => c * x ^ (2 ^ j) from by funext x; rw [h1, h2, mul_one]]
      exact affine_frob c j
    · have h1 : ((2 ^ i + 2 ^ j : ℕ) : K) = 0 := by
        rw [Nat.cast_add, natCast_two_pow i hi, natCast_two_pow j (by omega), add_zero]
      rw [show (fun x : K => c * ((2 ^ i + 2 ^ j : ℕ) : K) * x ^ (2 ^ i + 2 ^ j - 1)) =
        fun _ : K => (0 : K) from by funext x; rw [h1, mul_zero, zero_mul]]
      exact affine_zero

theorem term_hasse_affine (e : ℕ)
    (he : e = 0 ∨ (∃ i, e = 2 ^ i) ∨ (∃ i j, i < j ∧ e = 2 ^ i + 2 ^ j)) (c : K) :
    IsAffine (fun x : K => ((e.choose 2 : ℕ) : K) * c * x ^ (e - 2)) := by
  have hz : ∀ n : ℕ, ((n.choose 2 : ℕ) : K) = 0 → IsAffine (fun x : K => ((n.choose 2 : ℕ) : K) * c * x ^ (n - 2)) := by
    intro n h; rw [show (fun x : K => ((n.choose 2 : ℕ) : K) * c * x ^ (n - 2)) = fun _ => (0 : K) from
      by funext x; rw [h, zero_mul, zero_mul]]; exact affine_zero
  rcases he with rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · exact hz 0 (by simp)
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · exact hz _ (by simp)
      · intro x y; simp
    · apply hz
      rw [choose2_cast]
      have : 2 ^ i / 2 = 2 ^ (i - 1) := by
        obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
        rw [pow_succ]; simp
      rw [this]; exact natCast_two_pow _ (by omega)
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · -- e = 1 + 2^j
        rcases Nat.lt_or_ge j 2 with hj | hj
        · interval_cases j
          intro x y; norm_num [Nat.choose]; ring
        · apply hz
          rw [choose2_cast]
          have : (2 ^ 0 + 2 ^ j) / 2 = 2 ^ (j - 1) := by
            obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
            rw [Nat.add_sub_cancel, show 2 ^ 0 + 2 ^ (t + 1) = 1 + 2 ^ t * 2 by ring,
              Nat.add_mul_div_right _ _ (by norm_num)]
            norm_num
          rw [this]; exact natCast_two_pow _ (by omega)
      · -- e = 2 + 2^j, j ≥ 2
        have hj : 2 ≤ j := by omega
        have h1 : ((((2 ^ 1 + 2 ^ j).choose 2 : ℕ)) : K) = 1 := by
          rw [choose2_cast]
          have : (2 ^ 1 + 2 ^ j) / 2 = 1 + 2 ^ (j - 1) := by
            obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
            rw [Nat.add_sub_cancel, show 2 ^ 1 + 2 ^ (t + 1) = (1 + 2 ^ t) * 2 by ring,
              Nat.mul_div_cancel _ (by norm_num)]
          rw [this, Nat.cast_add, natCast_two_pow _ (by omega)]; simp
        have h2 : 2 ^ 1 + 2 ^ j - 2 = 2 ^ j := by simp
        intro x y
        simp only [h1, h2, one_mul]
        rw [frob_add, zero_pow (by positivity)]; ring
    · apply hz
      rw [choose2_cast]
      have : (2 ^ i + 2 ^ j) / 2 = 2 ^ (i - 1) + 2 ^ (j - 1) := by
        obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
        obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
        rw [Nat.add_sub_cancel, Nat.add_sub_cancel,
          show 2 ^ (t + 1) + 2 ^ (u + 1) = (2 ^ t + 2 ^ u) * 2 by ring, Nat.mul_div_cancel _ (by norm_num)]
      rw [this, Nat.cast_add, natCast_two_pow _ (by omega), natCast_two_pow _ (by omega), add_zero]

theorem deriv_affine (p : K[X]) (hq : IsQuadSupport p) : IsAffine (fun x => p.derivative.eval x) := by
  have := affine_sum p.support (fun e x => p.coeff e * (e : K) * x ^ (e - 1))
    (fun e he => term_deriv_affine e (hq e he) _)
  intro x y
  simp only [deriv_eval_sum]
  exact this x y

theorem hasse2_affine (p : K[X]) (hq : IsQuadSupport p) :
    IsAffine (fun x => (hasseDeriv 2 p).eval x) := by
  have := affine_sum p.support (fun e x => ((e.choose 2 : ℕ) : K) * p.coeff e * x ^ (e - 2))
    (fun e he => term_hasse_affine e (hq e he) _)
  intro x y
  simp only [hasse2_eval_sum]
  exact this x y

end field

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

theorem hyp_of_H [Fintype K] [DecidableEq K] (f : R[X]) (ρ : K)
    (hq : IsQuadSupport (f.map S.π))
    (hρ : ρ ≠ 0)
    (hker : ∀ x, (f.map S.π).derivative.eval x = (f.map S.π).derivative.eval 0 ↔ (x = 0 ∨ x = ρ))
    (hapn : ∀ b : K, (univ.filter (fun x : K => (f.map S.π).eval (x + ρ) - (f.map S.π).eval x = b)).card ≤ 2) :
    S.Hyp f ρ ((hasseDeriv 2 (f.map S.π)).eval ρ - (hasseDeriv 2 (f.map S.π)).eval 0) ∧
      (∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b → b = a ∨ b = a + ρ) := by
  haveI := S.charP2
  set p := f.map S.π
  have hD := deriv_affine p hq
  have hH := hasse2_affine p hq
  have h2 : (2 : K) = 0 := two_K
  have hpρ : p.derivative.eval ρ = p.derivative.eval 0 := (hker ρ).mpr (Or.inr rfl)
  have hper : ∀ a, p.derivative.eval (a + ρ) = p.derivative.eval a := by
    intro a; have := hD a ρ; simp only at this; rw [this, hpρ]; ring
  have hd2 : ∀ a b : K, p.derivative.eval a = p.derivative.eval b → b = a ∨ b = a + ρ := by
    intro a b hab
    have e := hD a (b - a)
    simp only [show a + (b - a) = b by ring] at e
    have : p.derivative.eval (b - a) = p.derivative.eval 0 := by linear_combination -e - hab
    rcases (hker _).mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hμ : ∀ a, (hasseDeriv 2 p).eval (a + ρ) - (hasseDeriv 2 p).eval a =
      (hasseDeriv 2 p).eval ρ - (hasseDeriv 2 p).eval 0 := by
    intro a; have := hH a ρ; simp only at this; rw [this]; ring
  have hρρ : ∀ a : K, a + ρ + ρ = a := fun a => by linear_combination ρ * h2
  have hdp : ∀ a b : K, p.eval (a + ρ) - p.eval a = p.eval (b + ρ) - p.eval b ↔ (b = a ∨ b = a + ρ) := by
    intro a b
    constructor
    · intro hab
      by_contra hne
      push Not at hne
      obtain ⟨hba, hbaρ⟩ := hne
      set c := p.eval (a + ρ) - p.eval a
      have hsub : ({a, a + ρ, b, b + ρ} : Finset K) ⊆
          univ.filter (fun x : K => p.eval (x + ρ) - p.eval x = c) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl | rfl | rfl
        · rfl
        · rw [hρρ]; linear_combination (p.eval a - p.eval (a + ρ)) * h2
        · exact hab.symm
        · rw [hρρ]; linear_combination -hab + (p.eval b - p.eval (b + ρ)) * h2
      have hcard4 : ({a, a + ρ, b, b + ρ} : Finset K).card = 4 := by
        have n1 : a ≠ a + ρ := by intro h; apply hρ; linear_combination -h
        have n2 : a ≠ b := fun h => hba h.symm
        have n3 : a ≠ b + ρ := by intro h; apply hbaρ; linear_combination -h - ρ * h2
        have n4 : a + ρ ≠ b := fun h => hbaρ h.symm
        have n5 : a + ρ ≠ b + ρ := by intro h; apply hba; linear_combination -h
        have n6 : b ≠ b + ρ := by intro h; apply hρ; linear_combination -h
        rw [Finset.card_insert_of_notMem (by simp [n1, n2, n3]),
          Finset.card_insert_of_notMem (by simp [n4, n5]),
          Finset.card_insert_of_notMem (by simp [n6]), Finset.card_singleton]
      have := le_trans (hcard4 ▸ Finset.card_le_card hsub) (hapn c)
      omega
    · rintro (rfl | rfl)
      · rfl
      · rw [hρρ]; linear_combination (p.eval (a + ρ) - p.eval a) * h2
  exact ⟨⟨hρ, hper, hμ, hdp⟩, hd2⟩

end GRS

end APN2

#print axioms APN2.deriv_affine
#print axioms APN2.hasse2_affine
#print axioms APN2.GRS.hyp_of_H
