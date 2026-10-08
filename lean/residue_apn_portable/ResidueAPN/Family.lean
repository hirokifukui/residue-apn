import ResidueAPN.Basic

/-!
# The family `P_{m,r}` as polynomials (paper_R5, Section 3 and Proposition 5.1)

The polynomials are defined over an arbitrary commutative ring `R` from `X`, `1`, `+` and `*`
only, so that `Polynomial.map` sends the family over `R` to the family over `S`
(`map_polP` …). Over `ZMod 2` this is "coefficients in `𝔽₂`"; over `ℤ` it is the `0/1` lift.

* `polV = ∑_{i < r-2} X^(2^i)`, `polW = X^(2^(r-2))`, `polY = X^(2^(m-2))`, `polZ = X^(2^(m-1))`,
  `polD = 1 + W + Y`, `polE = 1 + V + Y + Z`, `polP = V + W + W V + W Y + W Z + Y V + Y Z`,
  `polT = ∑_{i < r} X^(2^i)`.

Proved here:
* `polP_eq_int` (Proposition 5.1): `P = D E - 1 - 2 (Y + Z)` in every commutative ring, `m ≥ 2`.
* `polP_add_one` (Theorem 3.1(4), first half): `P + 1 = D E` in characteristic two.
* `derivative_polP` (Theorem 3.1(3), formal part): `P' = D` in characteristic two, `r ≥ 3`, `m ≥ 3`.
* `derivative_polE` (Theorem 3.1(4), second half): `E' = 1` in characteristic two.
-/

namespace ResidueAPN

open Polynomial Finset

section Defs

variable (R : Type*) [CommRing R] (m r : ℕ)

noncomputable def polV : R[X] := ∑ i ∈ range (r - 2), X ^ (2 ^ i)
noncomputable def polW : R[X] := X ^ (2 ^ (r - 2))
noncomputable def polY : R[X] := X ^ (2 ^ (m - 2))
noncomputable def polZ : R[X] := X ^ (2 ^ (m - 1))
noncomputable def polD : R[X] := 1 + polW R r + polY R m
noncomputable def polE : R[X] := 1 + polV R r + polY R m + polZ R m
noncomputable def polP : R[X] :=
  polV R r + polW R r + polW R r * polV R r + polW R r * polY R m + polW R r * polZ R m
    + polY R m * polV R r + polY R m * polZ R m
noncomputable def polT : R[X] := ∑ i ∈ range r, X ^ (2 ^ i)

end Defs

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (m r : ℕ)

@[simp] theorem map_polV : (polV R r).map f = polV S r := by simp [polV, Polynomial.map_sum]
@[simp] theorem map_polW : (polW R r).map f = polW S r := by simp [polW]
@[simp] theorem map_polY : (polY R m).map f = polY S m := by simp [polY]
@[simp] theorem map_polZ : (polZ R m).map f = polZ S m := by simp [polZ]
@[simp] theorem map_polD : (polD R m r).map f = polD S m r := by simp [polD]
@[simp] theorem map_polE : (polE R m r).map f = polE S m r := by simp [polE]
@[simp] theorem map_polP : (polP R m r).map f = polP S m r := by simp [polP]
@[simp] theorem map_polT : (polT R r).map f = polT S r := by simp [polT, Polynomial.map_sum]

end Map

section Identities

variable {R : Type*} [CommRing R] {m r : ℕ}

/-- `Y ^ 2 = Z` for `m ≥ 2`. -/
theorem polY_mul_self (hm : 2 ≤ m) : polY R m * polY R m = polZ R m := by
  unfold polY polZ
  rw [← pow_add, ← two_mul, ← pow_succ']
  congr 2
  omega

/-- **Proposition 5.1.** `P̂ = D̂ Ê - 1 - 2 (Ŷ + Ẑ)`, in every commutative ring (in particular
in `ℤ[X]`, and hence in `GR(2^k, m)[X]` by `Polynomial.map`). -/
theorem polP_eq_int (hm : 2 ≤ m) :
    polP R m r = polD R m r * polE R m r - 1 - 2 * (polY R m + polZ R m) := by
  have h := polY_mul_self (R := R) hm
  unfold polP polD polE
  linear_combination (-1 : R[X]) * h

/-- **Theorem 3.1(4), first half.** `P + 1 = D E` in characteristic two. -/
theorem polP_add_one [CharP R 2] (hm : 2 ≤ m) :
    polP R m r + 1 = polD R m r * polE R m r := by
  have h := polY_mul_self (R := R) hm
  have h2 : (2 : R[X]) = 0 := CharTwo.two_eq_zero
  unfold polP polD polE
  linear_combination (-1 : R[X]) * h + (-(polY R m + polZ R m) : R[X]) * h2

end Identities

section Derivative

variable {R : Type*} [CommRing R] [CharP R 2]

/-- In characteristic two, `(X ^ 2 ^ i)' = 0` for `i ≥ 1`. -/
theorem derivative_X_two_pow {i : ℕ} (hi : 1 ≤ i) : derivative (X ^ (2 ^ i) : R[X]) = 0 := by
  rw [derivative_X_pow]
  have : ((2 ^ i : ℕ) : R) = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [pow_add, pow_one, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul]
  simp [this]

theorem derivative_polV {r : ℕ} (hr : 3 ≤ r) : derivative (polV R r) = 1 := by
  unfold polV
  obtain ⟨k, hk⟩ : ∃ k, r - 2 = k + 1 := ⟨r - 3, by omega⟩
  rw [hk, Finset.sum_range_succ', derivative_add, derivative_sum]
  rw [Finset.sum_eq_zero (fun i _ => derivative_X_two_pow (R := R) (Nat.succ_le_succ (Nat.zero_le i)))]
  simp

theorem derivative_polW {r : ℕ} (hr : 3 ≤ r) : derivative (polW R r) = 0 :=
  derivative_X_two_pow (by omega)

theorem derivative_polY {m : ℕ} (hm : 3 ≤ m) : derivative (polY R m) = 0 :=
  derivative_X_two_pow (by omega)

theorem derivative_polZ {m : ℕ} (hm : 2 ≤ m) : derivative (polZ R m) = 0 :=
  derivative_X_two_pow (by omega)

/-- **Theorem 3.1(3), formal part.** `P' = D = 1 + X^(2^(r-2)) + X^(2^(m-2))`. -/
theorem derivative_polP {m r : ℕ} (hr : 3 ≤ r) (hm : 3 ≤ m) :
    derivative (polP R m r) = polD R m r := by
  unfold polP polD
  simp only [derivative_add, derivative_mul, derivative_polV hr, derivative_polW (R := R) hr,
    derivative_polY (R := R) hm, derivative_polZ (R := R) (by omega : 2 ≤ m)]
  ring

/-- **Theorem 3.1(4), second half.** `E' = 1`. -/
theorem derivative_polE {m r : ℕ} (hr : 3 ≤ r) (hm : 3 ≤ m) : derivative (polE R m r) = 1 := by
  unfold polE
  simp only [derivative_add, derivative_one, derivative_polV hr, derivative_polY (R := R) hm,
    derivative_polZ (R := R) (by omega : 2 ≤ m)]
  ring

end Derivative

end ResidueAPN
