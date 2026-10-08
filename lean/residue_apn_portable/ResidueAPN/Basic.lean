import ResidueAPN.Shared.QuadraticAPN
import ResidueAPN.Shared.ReducedRepresentative

/-!
# Part 1 — definitions and Frobenius helpers (paper_R5, Section 2)

* `IsDerivOptimal p` — Definition 2.1: `p'` has no zero on `F` and every (nonempty) fibre of
  `x ↦ p'(x)` has exactly two elements.
* `IsOptimalAPNPerm f` — APN, bijective, and the reduced representative `rep f` is
  derivative-optimal.

`IsAPN`, `IsQuadratic`, `deriv`, `rep` are the definitions of the apnlift development
(IT-26-1499, Supplement S1), copied unchanged into `ResidueAPN/Shared/`.

Throughout, `F` is a finite field of characteristic two with `card F = 2 ^ m`.
-/

namespace ResidueAPN

open Polynomial

section Defs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Definition 2.1 of paper_R5. A fibre through `x` is the set of `y` with `p'(y) = p'(x)`;
"every nonempty fibre has two elements" is "every fibre through a point has two elements". -/
def IsDerivOptimal (p : F[X]) : Prop :=
  (∀ x : F, (derivative p).eval x ≠ 0) ∧
  ∀ x : F, (Finset.univ.filter
      (fun y : F => (derivative p).eval y = (derivative p).eval x)).card = 2

/-- An optimal APN permutation (Definition 2.1 of paper_R5). -/
def IsOptimalAPNPerm [CharP F 2] (f : F → F) : Prop :=
  IsAPN f ∧ Function.Bijective f ∧ IsDerivOptimal (rep f)

end Defs

section Frobenius

variable {F : Type*} [Field F] [CharP F 2]

/-- The Frobenius power `x ↦ x ^ 2 ^ k` is additive. -/
theorem frob_add (k : ℕ) (a b : F) : (a + b) ^ (2 ^ k) = a ^ (2 ^ k) + b ^ (2 ^ k) :=
  add_pow_char_pow (R := F) a b 2 k

/-- The Frobenius power commutes with finite sums. -/
theorem frob_sum {ι : Type*} (s : Finset ι) (f : ι → F) (k : ℕ) :
    (∑ i ∈ s, f i) ^ (2 ^ k) = ∑ i ∈ s, f i ^ (2 ^ k) :=
  sum_pow_char_pow (R := F) (p := 2) (n := k) s f

/-- Iterating a Frobenius fixed point. -/
theorem pow_two_pow_mul_of_fixed {x : F} {m : ℕ} (h : x ^ (2 ^ m) = x) (t : ℕ) :
    x ^ (2 ^ (m * t)) = x := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

/-- If `x` is fixed by `x ↦ x ^ 2 ^ m`, then `x ^ 2 ^ n = x ^ 2 ^ (n % m)`. -/
theorem pow_two_pow_mod_of_fixed {x : F} {m : ℕ} (h : x ^ (2 ^ m) = x) (n : ℕ) :
    x ^ (2 ^ n) = x ^ (2 ^ (n % m)) := by
  conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, pow_two_pow_mul_of_fixed h]

/-- Fixed points of two Frobenius powers are fixed by the power of the gcd. -/
theorem pow_two_pow_gcd_of_fixed {x : F} :
    ∀ a b : ℕ, x ^ (2 ^ a) = x → x ^ (2 ^ b) = x → x ^ (2 ^ (Nat.gcd a b)) = x := by
  intro a b
  induction a, b using Nat.gcd.induction with
  | H0 n => intro _ hn; simpa using hn
  | H1 a b _ ih =>
      intro ha hb
      rw [Nat.gcd_rec]
      exact ih (by rw [← pow_two_pow_mod_of_fixed ha]; exact hb) ha

/-- If `x ^ 2 ^ r = x` and `x ^ 2 ^ m = x` with `gcd(r, m) = 1`, then `x ∈ {0, 1}`. -/
theorem eq_zero_or_one_of_fixed {x : F} {r m : ℕ} (hcop : Nat.Coprime r m)
    (hr : x ^ (2 ^ r) = x) (hm : x ^ (2 ^ m) = x) : x = 0 ∨ x = 1 := by
  have h2 : x ^ 2 = x := by
    have := pow_two_pow_gcd_of_fixed r m hr hm
    rwa [hcop.gcd_eq_one, pow_one] at this
  have : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h2, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- If `x ^ 2 ^ r = x + 1`, then `x ^ 2 ^ (r * k) = x + k`. -/
theorem pow_two_pow_mul_of_shift {x : F} {r : ℕ} (h : x ^ (2 ^ r) = x + 1) (k : ℕ) :
    x ^ (2 ^ (r * k)) = x + (k : F) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, frob_add, h, Nat.cast_succ]
      have : (k : F) ^ (2 ^ r) = (k : F) := by
        have := map_natCast (iterateFrobenius F 2 r) k
        rwa [iterateFrobenius_def] at this
      rw [this]; ring

/-- An odd natural number is `1` in characteristic two. -/
theorem natCast_of_odd {n : ℕ} (h : Odd n) : (n : F) = 1 := by
  obtain ⟨t, rfl⟩ := h
  push_cast
  rw [CharTwo.two_eq_zero, zero_mul, zero_add]

/-- In a field with `x ^ 2 ^ m = x` for all `x` and `m` odd, `x ^ 2 ^ r = x + 1` has no solution. -/
theorem no_shift_fixed {x : F} {r m : ℕ} (hm : x ^ (2 ^ m) = x) (hodd : Odd m) :
    x ^ (2 ^ r) ≠ x + 1 := by
  intro h
  have h1 := pow_two_pow_mul_of_shift h m
  rw [mul_comm, pow_two_pow_mul_of_fixed hm] at h1
  rw [natCast_of_odd hodd] at h1
  exact one_ne_zero (add_left_cancel (h1.symm.trans (add_zero x).symm))

end Frobenius

section FiniteField

variable {F : Type*} [Field F] [Fintype F]

/-- `x ^ 2 ^ m = x` on a field with `2 ^ m` elements. -/
theorem pow_card_two_pow {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (x : F) : x ^ (2 ^ m) = x := by
  rw [← hcard]; exact FiniteField.pow_card x

end FiniteField

end ResidueAPN
