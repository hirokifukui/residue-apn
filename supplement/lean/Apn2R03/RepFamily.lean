import Apn2R03.ResPerm

/-!
# Representatives with μ = 0 and Z = ∅: the function-level core of Theorem repfamily (Claude, 2026-10-26, R05b)

K a field with 2^m elements, m odd, A_d(x) = Tr(x) + d·x^{2^{m-2}}, d ≠ 0 with Tr(d) = Tr(d⁻¹) = 0, ρ = d⁻⁴.
* `Ad_add`, `Ad_inj`, `Ad_rho` : A_d is additive and injective, and A_d(ρ) = 1;
* `cubeAd_inj`                 : x ↦ A_d(x)³ is injective (a permutation);
* `Kd_zero_iff`                : K = A_d² + A_d vanishes exactly at 0 and ρ (so ker K = {0, ρ});
* `eps_not_im`                 : (1+d)² ∉ {w² + w} (ε ∉ Im K);
* `Lam_ne_zero`                : (1+ρ)(w² + w) + 1 + ρ(1+d)² never vanishes (Z = ∅).
The passage from the polynomial p_d to these functions (ε = (1+d)², K = A_d² + A_d, μ = a₀²r + a₁r² = 0 and the
formula for Λ, paper proof of Theorem repfamily) is on paper only.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset APN2R03

section repfamily
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- A_d(x) = Tr(x) + d x^{2^{m-2}} -/
def Ad (m : ℕ) (d x : K) : K := absTr m x + d * x ^ (2 ^ (m - 2))

theorem absTr_sq_self (m : ℕ) (hcard : Fintype.card K = 2 ^ m) (x : K) :
    absTr m x ^ 2 = absTr m x := by
  have e : absTr m x ^ 2 = absTr m (x ^ 2) := by
    unfold absTr
    rw [sum_sq_char2]
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e, absTr_sq m hcard]

theorem absTr_01 (m : ℕ) (hcard : Fintype.card K = 2 ^ m) (x : K) : absTr m x = 0 ∨ absTr m x = 1 := by
  have h := absTr_sq_self m hcard x
  have : absTr m x * (absTr m x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

theorem Ad_add (m : ℕ) (d x y : K) : Ad m d (x + y) = Ad m d x + Ad m d y := by
  unfold Ad; rw [absTr_add, frob_add]; ring

theorem pow_card_eq (m : ℕ) (hcard : Fintype.card K = 2 ^ m) (x : K) : x ^ (2 ^ m) = x := by
  rw [← hcard]; exact FiniteField.pow_card x

theorem two_pow_m4 (m : ℕ) (hm : 2 ≤ m) : 2 ^ (m - 2) * 4 = 2 ^ m := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hm]

theorem frob_m2 (m : ℕ) (hm : 2 ≤ m) (hcard : Fintype.card K = 2 ^ m) (y : K) :
    (y ^ 4) ^ (2 ^ (m - 2)) = y := by
  rw [← pow_mul, mul_comm, two_pow_m4 m hm]
  exact pow_card_eq m hcard y

theorem absTr_pow4 (m : ℕ) (hcard : Fintype.card K = 2 ^ m) (y : K) : absTr m (y ^ 4) = absTr m y := by
  have := absTr_pow_two_pow m hcard y 2
  norm_num at this
  exact this

theorem Ad_rho (m : ℕ) (hm : 2 ≤ m) (hcard : Fintype.card K = 2 ^ m) (d : K) (hd : d ≠ 0)
    (htri : absTr m d⁻¹ = 0) : Ad m d (d⁻¹ ^ 4) = 1 := by
  unfold Ad
  rw [absTr_pow4 m hcard, htri, zero_add, frob_m2 m hm hcard, mul_inv_cancel₀ hd]

theorem Ad_inj (m : ℕ) (hm : 2 ≤ m) (hcard : Fintype.card K = 2 ^ m) (d : K) (hd : d ≠ 0)
    (htri : absTr m d⁻¹ = 0) (x : K) (hx : Ad m d x = 0) : x = 0 := by
  have h2 : (2 : K) = 0 := two_K
  unfold Ad at hx
  rcases absTr_01 m hcard x with ht | ht
  · rw [ht, zero_add] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h hd
    · exact pow_eq_zero_iff (by positivity) |>.mp h
  · exfalso
    rw [ht] at hx
    have hdy : d * x ^ (2 ^ (m - 2)) = 1 := by linear_combination hx - h2
    -- raise to the 4th power: d^4 x^{2^m} = 1, so x = d⁻⁴
    have h4 : d ^ 4 * x = 1 := by
      have := congrArg (· ^ 4) hdy
      simp only [one_pow, mul_pow] at this
      rw [← pow_mul, two_pow_m4 m hm, pow_card_eq m hcard] at this
      exact this
    have hxd : x = d⁻¹ ^ 4 := by
      rw [inv_pow]; field_simp; linear_combination h4
    rw [hxd, absTr_pow4 m hcard, htri] at ht
    exact zero_ne_one ht

theorem cubeAd_inj (m : ℕ) (hm : 2 ≤ m) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (d : K)
    (hd : d ≠ 0) (htri : absTr m d⁻¹ = 0) (x y : K) (h : Ad m d x ^ 3 = Ad m d y ^ 3) : x = y := by
  have h2 : (2 : K) = 0 := two_K
  have e := cube_inj m hodd hcard _ _ h
  have : Ad m d (x - y) = 0 := by
    have hs : x - y = x + y := by linear_combination (-y) * h2
    rw [hs, Ad_add, e]; linear_combination (Ad m d y) * h2
  have := Ad_inj m hm hcard d hd htri _ this
  linear_combination this

/-- K = A_d² + A_d vanishes exactly at 0 and ρ = d⁻⁴ -/
theorem Kd_zero_iff (m : ℕ) (hm : 2 ≤ m) (hcard : Fintype.card K = 2 ^ m) (d : K) (hd : d ≠ 0)
    (htri : absTr m d⁻¹ = 0) (y : K) :
    Ad m d y ^ 2 + Ad m d y = 0 ↔ (y = 0 ∨ y = d⁻¹ ^ 4) := by
  have h2 : (2 : K) = 0 := two_K
  have hr := Ad_rho m hm hcard d hd htri
  constructor
  · intro h
    have : Ad m d y * (Ad m d y + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl (Ad_inj m hm hcard d hd htri y h0)
    · right
      have : Ad m d (y + d⁻¹ ^ 4) = 0 := by rw [Ad_add, hr]; linear_combination h1
      have := Ad_inj m hm hcard d hd htri _ this
      linear_combination this - (d⁻¹ ^ 4) * h2
  · rintro (rfl | rfl)
    · have : Ad m d 0 = 0 := by
        have := Ad_add m d 0 0; rw [add_zero] at this; linear_combination -this
      rw [this]; ring
    · rw [hr]; linear_combination h2

/-- ε = (1+d)² is not of the form w² + w (Im K = ker Tr) when Tr d = 0 -/
theorem eps_not_im (m : ℕ) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (d : K) (htr : absTr m d = 0)
    (w : K) : w ^ 2 + w ≠ (1 + d) ^ 2 := by
  intro h
  have h0 := absTr_artin_schreier m hcard w
  rw [h, absTr_sq m hcard, absTr_add, absTr_one m hodd, htr, add_zero] at h0
  exact one_ne_zero h0

/-- **Z = ∅**: Λ = (1+ρ)(w² + w) + 1 + ρ(1+d)² has no zero (ρ = d⁻⁴), for every w -/
theorem Lam_ne_zero (m : ℕ) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (d : K) (hd : d ≠ 0)
    (htri : absTr m d⁻¹ = 0) (w : K) :
    (1 + d⁻¹ ^ 4) * (w ^ 2 + w) + 1 + d⁻¹ ^ 4 * (1 + d) ^ 2 ≠ 0 := by
  have h2 : (2 : K) = 0 := two_K
  have hd1 : d + 1 ≠ 0 := by
    intro h
    have : d = 1 := by linear_combination h - h2
    rw [this, inv_one, absTr_one m hodd] at htri
    exact one_ne_zero htri
  intro hz
  set u := (d + 1)⁻¹ with hu
  have hu1 : u * (d + 1) = 1 := inv_mul_cancel₀ hd1
  set v := u ^ 2 + u with hv
  -- (d+1)^2 v = d
  have hv2 : (d + 1) ^ 2 * v = d := by
    have : (d + 1) ^ 2 * v = (u * (d + 1)) ^ 2 + (u * (d + 1)) * (d + 1) := by rw [hv]; ring
    rw [this, hu1]; linear_combination h2
  -- multiply hz by d^4: (d+1)^4 (w^2+w) = (d+1)^4 + d^2
  have hd4 : d ^ 4 * d⁻¹ ^ 4 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  have key : (d + 1) ^ 4 * (w ^ 2 + w) = (d + 1) ^ 4 + d ^ 2 := by
    have e := congrArg (fun t => d ^ 4 * t) hz
    simp only [mul_zero] at e
    have e2 : d ^ 4 * ((1 + d⁻¹ ^ 4) * (w ^ 2 + w) + 1 + d⁻¹ ^ 4 * (1 + d) ^ 2) =
        (d ^ 4 + 1) * (w ^ 2 + w) + d ^ 4 + (1 + d) ^ 2 := by
      linear_combination ((w ^ 2 + w) + (1 + d) ^ 2) * hd4
    rw [e2] at e
    linear_combination e + ((2 * d ^ 3 + 3 * d ^ 2 + 2 * d) * (w ^ 2 + w)
      - (d ^ 4 + 2 * d ^ 3 + 4 * d ^ 2 + 3 * d + 1)) * h2
  -- hence w^2 + w = 1 + v^2
  have hX : w ^ 2 + w = 1 + v ^ 2 := by
    have h4 : (d + 1) ^ 4 ≠ 0 := pow_ne_zero 4 hd1
    apply mul_left_cancel₀ h4
    have : (d + 1) ^ 4 * v ^ 2 = d ^ 2 := by rw [show (d + 1) ^ 4 * v ^ 2 = ((d + 1) ^ 2 * v) ^ 2 by ring, hv2]
    linear_combination key - this
  have t1 := absTr_artin_schreier m hcard w
  rw [hX, absTr_add, absTr_one m hodd, absTr_sq m hcard, hv, absTr_artin_schreier m hcard u, add_zero] at t1
  exact one_ne_zero t1

end repfamily

end APN2

#print axioms APN2.Ad_inj
#print axioms APN2.Ad_rho
#print axioms APN2.cubeAd_inj
#print axioms APN2.Kd_zero_iff
#print axioms APN2.eps_not_im
#print axioms APN2.Lam_ne_zero
