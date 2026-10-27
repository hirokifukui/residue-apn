import Apn2R03.HypFromH
import Apn2R03.Spectrum4
import Apn2R03.MainK4

/-!
# Tools for the explicit family (Claude, 2026-10-25)

* `frob_gcd` : x^(2^a) = x ∧ x^(2^b) = x ⇒ x^(2^gcd(a,b)) = x.
* trace lemmas: additivity, Frobenius invariance, Tr(1) = 1 for odd m.
* `Q4`: computations modulo 4 through the quotient R ⧸ (4).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

section frob
variable {K : Type*} [Field K]

theorem pow_two_pow_iter (x : K) (a : ℕ) (ha : x ^ (2 ^ a) = x) : ∀ n, x ^ (2 ^ (a * n)) = x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, ha]

theorem frob_gcd (x : K) : ∀ a b : ℕ, x ^ (2 ^ a) = x → x ^ (2 ^ b) = x → x ^ (2 ^ Nat.gcd a b) = x := by
  intro a b
  induction a, b using Nat.gcd.induction with
  | H0 n => intro _ hn; simpa using hn
  | H1 m n hm ih =>
    intro hxm hxn
    have hr : x ^ (2 ^ (n % m)) = x := by
      have e : n = m * (n / m) + n % m := (Nat.div_add_mod n m).symm
      have h1 : x ^ (2 ^ n) = (x ^ (2 ^ (m * (n / m)))) ^ (2 ^ (n % m)) := by
        rw [← pow_mul, ← pow_add, ← e]
      rw [pow_two_pow_iter x m hxm, hxn] at h1
      exact h1.symm
    rw [Nat.gcd_rec]
    exact ih hr hxm

end frob

section trace
variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem absTr_add (m : ℕ) (x y : K) :
    APN2R03.absTr m (x + y) = APN2R03.absTr m x + APN2R03.absTr m y := by
  unfold APN2R03.absTr
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => frob_add i x y)

theorem absTr_sq (m : ℕ) (hm : Fintype.card K = 2 ^ m) (x : K) :
    APN2R03.absTr m (x ^ 2) = APN2R03.absTr m x := by
  unfold APN2R03.absTr
  have hshift : ∀ i, (x ^ 2) ^ (2 ^ i) = x ^ (2 ^ (i + 1)) := by
    intro i; rw [← pow_mul, pow_succ']
  simp_rw [hshift]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun i => x ^ 2 ^ i)]
    have : x ^ (2 ^ (n + 1)) = x := by rw [← hm, FiniteField.pow_card]
    rw [this]; simp

theorem absTr_pow_two_pow (m : ℕ) (hm : Fintype.card K = 2 ^ m) (x : K) :
    ∀ j, APN2R03.absTr m (x ^ (2 ^ j)) = APN2R03.absTr m x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_mul, absTr_sq m hm, ih]

theorem absTr_one (m : ℕ) (hodd : Odd m) : APN2R03.absTr m (1 : K) = 1 := by
  unfold APN2R03.absTr
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  obtain ⟨t, rfl⟩ := hodd
  push_cast
  have h2 : (2 : K) = 0 := two_K
  rw [h2]; ring

theorem absTr_zero (m : ℕ) : APN2R03.absTr m (0 : K) = 0 := by
  unfold APN2R03.absTr
  apply Finset.sum_eq_zero
  intro i _
  exact zero_pow (by positivity)

end trace

section Q4
variable {R : Type*} [CommRing R]

/-- the quotient ring R ⧸ (4) -/
abbrev Q4 (R : Type*) [CommRing R] := R ⧸ Ideal.span {(4 : R)}

theorem four_Q4 : (4 : Q4 R) = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {(4 : R)}) (4 : R)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [← map_ofNat (Ideal.Quotient.mk (Ideal.span {(4 : R)})) 4]
  exact h

theorem lift_Q4 (a b : R) (h : (Ideal.Quotient.mk (Ideal.span {(4 : R)}) a) =
    Ideal.Quotient.mk (Ideal.span {(4 : R)}) b) : ∃ w, a = b + 4 * w := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by linear_combination hw⟩

end Q4

end APN2

#print axioms APN2.frob_gcd
#print axioms APN2.absTr_pow_two_pow
#print axioms APN2.absTr_one
#print axioms APN2.lift_Q4
