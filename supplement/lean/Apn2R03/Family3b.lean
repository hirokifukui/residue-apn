import Apn2R03.Family3a

/-!
# The family P_{m,3}: Galois-ring level (Claude, 2026-10-25)

A_F and E_F of the natural lift, mod-4 computations in Q4 R = R ⧸ (4).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

section ring
variable {T : Type*} [CommRing T]

theorem deriv_X_pow_evalT (n : ℕ) (x : T) : ((X : T[X]) ^ n).derivative.eval x = (n : T) * x ^ (n - 1) := by
  simp [derivative_X_pow]

theorem fnat3_evalT (m : ℕ) (x : T) : (Fnat3 T m).eval x =
    x + x ^ 2 + x ^ 3 + x * x ^ (2 ^ (m - 2)) + x ^ 2 * x ^ (2 ^ (m - 2)) + x ^ 2 * x ^ (2 ^ (m - 1))
      + x ^ (2 ^ (m - 2)) * x ^ (2 ^ (m - 1)) := by
  simp only [Fnat3, eval_add, eval_pow, eval_X]
  ring

theorem two_pow_q4 (h4 : (4 : T) = 0) (n : ℕ) (hn : 2 ≤ n) : (2 : T) ^ n = 0 := by
  rw [show n = 2 + (n - 2) by omega, pow_add, show (2 : T) ^ 2 = 4 by norm_num, h4, zero_mul]

theorem fnat3_derivT (h4 : (4 : T) = 0) (m : ℕ) (hm : 4 ≤ m) (x : T) :
    (Fnat3 T m).derivative.eval x = 1 + 2 * x + 3 * x ^ 2 + x ^ (2 ^ (m - 2))
      + 2 * x * x ^ (2 ^ (m - 2)) + 2 * x * x ^ (2 ^ (m - 1)) := by
  simp only [Fnat3, derivative_add, eval_add, deriv_X_pow_evalT, derivative_X, eval_one]
  have e1 : 1 + 2 ^ (m - 2) - 1 = 2 ^ (m - 2) := by generalize 2 ^ (m - 2) = w; omega
  have e2 : 2 + 2 ^ (m - 2) - 1 = 1 + 2 ^ (m - 2) := by generalize 2 ^ (m - 2) = w; omega
  have e3 : 2 + 2 ^ (m - 1) - 1 = 1 + 2 ^ (m - 1) := by generalize 2 ^ (m - 1) = w; omega
  rw [e1, e2, e3]
  push_cast
  rw [two_pow_q4 h4 (m - 2) (by omega), two_pow_q4 h4 (m - 1) (by omega)]
  norm_num
  ring

theorem shiftU (h4 : (4 : T) = 0) (m : ℕ) (hm : 4 ≤ m) (x : T) :
    (x + 1) ^ (2 ^ (m - 2)) = x ^ (2 ^ (m - 2)) + 1 + 2 * x ^ (2 ^ (m - 3)) := by
  have := binom_mod4 h4 x (m - 3)
  rwa [show m - 3 + 1 = m - 2 by omega] at this

theorem shiftV (h4 : (4 : T) = 0) (m : ℕ) (hm : 4 ≤ m) (x : T) :
    (x + 1) ^ (2 ^ (m - 1)) = x ^ (2 ^ (m - 1)) + 1 + 2 * x ^ (2 ^ (m - 2)) := by
  have := binom_mod4 h4 x (m - 2)
  rwa [show m - 2 + 1 = m - 1 by omega] at this

theorem fnat3_A_ring (h4 : (4 : T) = 0) (m : ℕ) (hm : 5 ≤ m) (x : T) :
    (Fnat3 T m).derivative.eval (x + 1) - (Fnat3 T m).derivative.eval x =
      2 * (1 + x + x ^ (2 ^ (m - 3)) + x ^ (2 ^ (m - 2)) + x ^ (2 ^ (m - 1))) := by
  rw [fnat3_derivT h4 m (by omega), fnat3_derivT h4 m (by omega), shiftU h4 m (by omega),
    shiftV h4 m (by omega)]
  have := A_r3 h4 x (x ^ (2 ^ (m - 3))) (x ^ (2 ^ (m - 2))) (x ^ (2 ^ (m - 1)))
  linear_combination this

theorem UV_sq (m : ℕ) (hm : 3 ≤ m) (x : T) : (x ^ (2 ^ (m - 2))) ^ 2 = x ^ (2 ^ (m - 1)) := by
  rw [← pow_mul, ← pow_succ]; congr 2; omega

theorem YU_sq (m : ℕ) (hm : 4 ≤ m) (x : T) : (x ^ (2 ^ (m - 3))) ^ 2 = x ^ (2 ^ (m - 2)) := by
  rw [← pow_mul, ← pow_succ]; congr 2; omega

theorem fnat3_E_ring (h4 : (4 : T) = 0) (m : ℕ) (hm : 5 ≤ m) (x : T) :
    (Fnat3 T m).eval (x + 1) - (Fnat3 T m).eval x - (Fnat3 T m).derivative.eval x =
      2 * (1 + x ^ 2 + x ^ (2 ^ (m - 2)) + x ^ (2 ^ (m - 3)) + x * x ^ (2 ^ (m - 3))
        + x ^ 2 * x ^ (2 ^ (m - 3)) + x ^ 2 * x ^ (2 ^ (m - 2))
        + x ^ (2 ^ (m - 3)) * x ^ (2 ^ (m - 1))) := by
  rw [fnat3_evalT, fnat3_evalT, fnat3_derivT h4 m (by omega), shiftU h4 m (by omega),
    shiftV h4 m (by omega)]
  have := Enat_numerator h4 x (x ^ (2 ^ (m - 3))) (x ^ (2 ^ (m - 2))) (x ^ (2 ^ (m - 1)))
    (UV_sq m (by omega) x)
  linear_combination this

end ring

section quot
variable {R : Type*} [CommRing R]

theorem mk4_eval (P : R[X]) (y : R) :
    Ideal.Quotient.mk (Ideal.span {(4 : R)}) (P.eval y) =
      (P.map (Ideal.Quotient.mk (Ideal.span {(4 : R)}))).eval (Ideal.Quotient.mk _ y) := by
  rw [eval_map, eval₂_at_apply]

theorem fnat3_A_R (m : ℕ) (hm : 5 ≤ m) (x : R) : ∃ w : R,
    (Fnat3 R m).derivative.eval (x + 1) - (Fnat3 R m).derivative.eval x =
      2 * (1 + x + x ^ (2 ^ (m - 3)) + x ^ (2 ^ (m - 2)) + x ^ (2 ^ (m - 1))) + 4 * w := by
  apply lift_Q4
  rw [map_sub, mk4_eval, mk4_eval, ← derivative_map, Fnat3_map, map_add, map_one,
    fnat3_A_ring four_Q4 m hm]
  simp only [map_mul, map_add, map_pow, map_one, map_ofNat]

theorem fnat3_E_R (m : ℕ) (hm : 5 ≤ m) (x : R) : ∃ w : R,
    (Fnat3 R m).eval (x + 1) - (Fnat3 R m).eval x - (Fnat3 R m).derivative.eval x =
      2 * (1 + x ^ 2 + x ^ (2 ^ (m - 2)) + x ^ (2 ^ (m - 3)) + x * x ^ (2 ^ (m - 3))
        + x ^ 2 * x ^ (2 ^ (m - 3)) + x ^ 2 * x ^ (2 ^ (m - 2))
        + x ^ (2 ^ (m - 3)) * x ^ (2 ^ (m - 1))) + 4 * w := by
  apply lift_Q4
  rw [map_sub, map_sub, mk4_eval, mk4_eval, mk4_eval, ← derivative_map, Fnat3_map, map_add, map_one,
    fnat3_E_ring four_Q4 m hm]
  simp only [map_mul, map_add, map_pow, map_one, map_ofNat]

end quot

end APN2
