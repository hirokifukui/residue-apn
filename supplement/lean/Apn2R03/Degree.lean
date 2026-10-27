import Apn2R03.Family3a
import Apn2R03.Family5a

/-!
# Degree statement of Theorem A (Claude, 2026-10-25, R04 follow-up)

Over any nontrivial commutative ring `R` and for `m ≥ 5` (and `5 ≤ r < m` for the second family):
the natural lift has degree `2^(m-2) + 2^(m-1) = 3q/4`, and the one-term correction does not raise it:
* `natDegree_Fnat3`, `natDegree_Fsh3` : r = 3, correction `2·(X^(2+2^(m-2)))^2 = 2·X^(4+2^(m-1))`;
* `natDegree_F5`, `natDegree_Fsh5`   : r ≥ 5, correction `2·X^3`.
The operation count ("one ring multiplication and two additions") is not formalized.
-/

namespace APN2

open Polynomial Finset

variable {R : Type*} [CommRing R] [Nontrivial R]

private theorem tw (m : ℕ) (hm : 5 ≤ m) : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
  rw [← pow_succ']; congr 1; omega

private theorem big (m : ℕ) (hm : 5 ≤ m) : 8 ≤ 2 ^ (m - 2) := by
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem natDegree_Fnat3 (m : ℕ) (hm : 5 ≤ m) :
    (Fnat3 R m).natDegree = 2 ^ (m - 2) + 2 ^ (m - 1) := by
  have h1 := tw m hm; have h2 := big m hm
  unfold Fnat3
  rw [natDegree_add_eq_right_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
      · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
        · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
          · exact lt_of_le_of_lt natDegree_X_le (by omega)
          · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
        · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
      · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
    · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
  · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)

theorem natDegree_Fsh3 (m : ℕ) (hm : 5 ≤ m) :
    (Fsh3 R m).natDegree = 2 ^ (m - 2) + 2 ^ (m - 1) := by
  have h1 := tw m hm; have h2 := big m hm
  unfold Fsh3
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_Fnat3 m hm]
  rw [natDegree_Fnat3 m hm]
  unfold J3
  refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
  rw [← pow_mul]
  exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)

theorem natDegree_F5 (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) (hrm : r < m) :
    (F5 R m r).natDegree = 2 ^ (m - 2) + 2 ^ (m - 1) := by
  have h1 := tw m hm; have h2 := big m hm
  have h3 : 2 ^ (r - 2) < 2 ^ (m - 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hZ : (Z5 R m r).natDegree < 2 ^ (m - 2) + 2 ^ (m - 1) := by
    unfold Z5
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 2 ^ (m - 2) + 2 ^ (m - 2) / 2) ?_)
      (by omega)
    intro i hi
    have hi' : i + 2 < m - 2 := by rw [mem_range] at hi; omega
    have h4 : 2 ^ (i + 2) ≤ 2 ^ (m - 2) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num), ← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ (r - 2) ≤ 2 ^ (m - 2) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num), ← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · exact le_trans (natDegree_X_pow_le _) (by omega)
      · exact le_trans (natDegree_X_pow_le _) (by omega)
    · exact le_trans (natDegree_X_pow_le _) (by omega)
  unfold F5
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · rw [natDegree_add_eq_right_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow]
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
      · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
        · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
          · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
            · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
              · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
                · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
                  · exact lt_of_le_of_lt natDegree_X_le (by omega)
                  · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
                · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
              · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
            · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
          · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
        · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
      · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
    · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
  · rw [natDegree_add_eq_right_of_natDegree_lt, natDegree_X_pow]
    · exact hZ
    · rw [natDegree_X_pow]
      refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
      · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
        · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
          · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
            · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
              · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
                · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
                  · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
                    · exact lt_of_le_of_lt natDegree_X_le (by omega)
                    · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
                  · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
                · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
              · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
            · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
          · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
        · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)
      · exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)

theorem natDegree_Fsh5 (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) (hrm : r < m) :
    (Fsh5 R m r).natDegree = 2 ^ (m - 2) + 2 ^ (m - 1) := by
  have h1 := tw m hm; have h2 := big m hm
  unfold Fsh5
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_F5 m r hm hr hrm]
  rw [natDegree_F5 m r hm hr hrm]
  refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
  exact lt_of_le_of_lt (natDegree_X_pow_le _) (by omega)

end APN2
