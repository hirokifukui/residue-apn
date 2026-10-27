import Apn2R03.CryptoCor

/-!
# The residues P_{m,r} are permutations; hypothesis-free crypto corollary (Claude, 2026-10-25, R04b)

* `cube_inj`   : x ↦ x³ is injective on a field with 2^m elements, m odd.
* `resPerm3`, `resPerm5` : the residue maps of the explicit family are permutations (p = Y³, Y additive and injective).
* `char_prob_le_fam3'`, `char_prob_le_fam5'` : Corollary crypto for F♯ without the injectivity hypothesis.
-/


set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

section perm
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

theorem two_pow_odd_mod3 (m : ℕ) (hm : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨t, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem cube_inj (m : ℕ) (hm : Odd m) (hcard : Fintype.card K = 2 ^ m) (x y : K) (h : x ^ 3 = y ^ 3) :
    x = y := by
  by_cases hy : y = 0
  · subst hy
    have : x ^ 3 = 0 := by rw [h]; ring
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  · have hz : (x / y) ^ 3 = 1 := by rw [div_pow, h, div_self (pow_ne_zero 3 hy)]
    have hx : x ≠ 0 := by
      intro hx0; rw [hx0] at hz; simp at hz
    have hq : (x / y) ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ (div_ne_zero hx hy)
    have hg : Nat.gcd 3 (Fintype.card K - 1) = 1 := by
      rw [hcard]
      have h1 := two_pow_odd_mod3 m hm
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hp : Nat.Prime 3 := by norm_num
      rcases Nat.coprime_or_dvd_of_prime hp (2 ^ m - 1) with hc | hd
      · exact hc
      · exfalso; omega
    have := (pow_gcd_eq_one (a := x / y)).mpr ⟨hz, hq⟩
    rw [hg, pow_one] at this
    exact (div_eq_one_iff_eq hy).mp this

theorem inj_of_add_ker {Y : K → K} (hadd : ∀ x y, Y (x + y) = Y x + Y y) (hker : ∀ x, Y x = 0 → x = 0) :
    Function.Injective Y := by
  intro x y hxy
  have h : Y (x - y) = 0 := by
    have := hadd (x - y) y
    rw [sub_add_cancel, hxy] at this
    linear_combination -this
  exact sub_eq_zero.mp (hker _ h)

theorem resPerm3 (m : ℕ) (hm5 : 5 ≤ m) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) :
    Function.Injective (fun t : K => (Fnat3 K m).eval t) := by
  intro x y hxy
  have h : Y3 m x ^ 3 = Y3 m y ^ 3 := by
    rw [← p3_cube m (by omega) hcard, ← p3_cube m (by omega) hcard]; exact hxy
  exact inj_of_add_ker (Y3_add m) (Y3_inj m (by omega) hcard h3) (cube_inj m hodd hcard _ _ h)

theorem resPerm5 (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (hrodd : Odd r) :
    Function.Injective (fun t : K => (F5 K m r).eval t) := by
  intro x y hxy
  have h : Y5 m r x ^ 3 = Y5 m r y ^ 3 := by
    rw [← p5_cube m r (by omega) (by omega) hcard, ← p5_cube m r (by omega) (by omega) hcard]; exact hxy
  exact inj_of_add_ker (Y5_add m r) (Y5_inj m r (by omega) (by omega) hcard hcop hrodd)
    (cube_inj m hodd hcard _ _ h)

end perm

namespace Markov

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

open scoped Classical in
/-- **Corollary crypto for F♯ (r = 3)**, no extra hypothesis on the residue map. -/
theorem char_prob_le_fam3' (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m : ℕ) (hm5 : 5 ≤ m) (hodd : Odd m) (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Δ : ℕ → (Fin n → R)) (N B : ℕ)
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hΔ : ∃ j, S0.π (Δ 0 j) ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => (APN2.Fsh3 R m).eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤
      (((2 * Fintype.card K : ℕ) : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  refine char_prob_le_fam3 S0 hcard m hm5 hodd hm h3 M Δ N B ?_ Mbar hM hB hΔ
  haveI := S0.charP2
  rw [S0.fam3_sh_map m]
  exact resPerm3 m hm5 hodd hm h3

open scoped Classical in
/-- **Corollary crypto for F♯ (r ≥ 5)**, no extra hypothesis on the residue map. -/
theorem char_prob_le_fam5' (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Δ : ℕ → (Fin n → R)) (N B : ℕ)
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hΔ : ∃ j, S0.π (Δ 0 j) ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤
      (((2 * Fintype.card K : ℕ) : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  refine char_prob_le_fam5 S0 hcard m r hm5 hr5 hrm hodd hmodd hm hcop M Δ N B ?_ Mbar hM hB hΔ
  haveI := S0.charP2
  rw [S0.fam5_sh_map m r]
  exact resPerm5 m r hm5 hr5 hmodd hm hcop hodd

end Markov

end APN2
