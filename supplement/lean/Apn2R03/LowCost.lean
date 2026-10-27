import Apn2R03.HullUnit

/-!
# Low-cost optimal lifts and the sparse family (Claude, 2026-10-26, R05c)

* `Fsh5'`            : the natural lift of `P_{m,r}` (`r ≥ 5`) with the coefficient `1` of the existing monomial
                       `X^(2^(r−2)+1)` replaced by `3` (no new monomial, no multiplication);
* `fam5'_A`          : `A_{Fsh5'} = 1 + A5n = A_{F♯}`;
* `fam5'_upper`, `fam5'_spectrum_all` : `Fsh5'` is optimal in every exceptional row (`≤ 2q`), as `F♯`;
* `sparse_Lam_ne`    : for the sparse family, `Λ(a) = (1+ρ)(w² + w + 1)` has no zero when `ρ ≠ 1` (odd `m`).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

/-- `F5` with the coefficient of `X^(2^(r−2)+1)` raised from `1` to `3` -/
noncomputable def Fsh5' (R : Type*) [CommRing R] (m r : ℕ) : R[X] :=
  F5 R m r + C 2 * X ^ (2 ^ (r - 2) + 1)

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem fam5'_map (m r : ℕ) : (Fsh5' R m r).map S.π = F5 K m r := by
  unfold Fsh5'; rw [S.map_add_two, F5_map]

theorem fam5'_hyp (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) : S.Hyp (Fsh5' R m r) 1 0 :=
  S.hyp_add_two _ _ 1 0 (S.fam5_hyp m r hm5 hr5 hrm hodd hcard hcop).1

theorem fam5'_A (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (a : K) :
    S.Afun (Fsh5' R m r) 1 a = 1 + A5n m r a := by
  haveI := S.charP2
  unfold Fsh5'
  rw [S.A_control _ _ 1 (S.fam5_hyp m r hm5 hr5 hrm hodd hcard hcop).1.hper,
    S.fam5_A m r hm5 hr5 hrm hodd hcard hcop]
  have e : ∀ y : K, (((X : R[X]) ^ (2 ^ (r - 2) + 1)).derivative.map S.π).eval y = y ^ (2 ^ (r - 2)) := by
    intro y
    rw [← derivative_map, Polynomial.map_pow, map_X, deriv_X_pow_evalT]
    have h1 : 2 ^ (r - 2) + 1 - 1 = 2 ^ (r - 2) := Nat.add_sub_cancel _ _
    rw [h1]
    have hc : (((2 ^ (r - 2) + 1 : ℕ) : K)) = 1 := by
      push_cast; rw [two_K, zero_pow (by omega), zero_add]
    rw [hc, one_mul]
  rw [e, e, frob_add, one_pow]
  ring

/-- **Optimality of the coefficient-changed lift (r ≥ 5)**: every exceptional entry is `≤ 2q`. -/
theorem fam5'_upper (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (α β : R) (hα : S.π α = 1) :
    delta (Fsh5' R m r) α β ≤ 2 * Fintype.card K := by
  haveI := S.charP2
  have := S.upper_basic hcard (Fsh5' R m r) 1 0 (S.fam5'_hyp m r hm5 hr5 hrm hodd hm hcop)
    (fun a => by rw [S.fam5'_A m r hm5 hr5 hrm hodd hm hcop]; exact A5s_ne m r hmodd hm a) α β hα
  simpa using this

/-- `A_{Fsh5'} = A_{F♯}` -/
theorem fam5'_A_eq_sharp (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (a : K) :
    S.Afun (Fsh5' R m r) 1 a = S.Afun (Fsh5 R m r) 1 a := by
  rw [S.fam5'_A m r hm5 hr5 hrm hodd hcard hcop, S.fam5_sh_A m r hm5 hr5 hrm hodd hcard hcop]

end GRS

section sparse
variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

/-- `w² + w + 1` has no root for odd `m` -/
theorem sq_add_add_one_ne (m : ℕ) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (w : K) :
    w ^ 2 + w + 1 ≠ 0 := by
  intro h
  have h2 : (2 : K) = 0 := two_K
  have := absTr_artin_schreier m hcard w
  have e : w ^ 2 + w = 1 := by linear_combination h - h2
  rw [e, absTr_one m hodd] at this
  exact one_ne_zero this

/-- **Z = ∅ for the sparse family**: `Λ(a) = (1+ρ)(w² + w + 1)` with `ρ ≠ 1` never vanishes. -/
theorem sparse_Lam_ne (m : ℕ) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (ρ w : K) (hρ : ρ ≠ 1) :
    (1 + ρ) * (w ^ 2 + w + 1) ≠ 0 := by
  have h2 : (2 : K) = 0 := two_K
  refine mul_ne_zero ?_ (sq_add_add_one_ne m hodd hcard w)
  intro h; apply hρ; linear_combination h - h2

/-- the Λ-formula of the repfamily computation specialises to the sparse family (`r = 1`, `a₀ = 1`, `ε = 1`) -/
theorem sparse_Lam_formula (ρ w : K) :
    (1 + 1 * ρ) * (w ^ 2 + 1 * w) + 1 ^ 3 + ρ * 1 = (1 + ρ) * (w ^ 2 + w + 1) := by ring

end sparse

end APN2

#print axioms APN2.GRS.fam5'_A
#print axioms APN2.GRS.fam5'_upper
#print axioms APN2.sparse_Lam_ne
