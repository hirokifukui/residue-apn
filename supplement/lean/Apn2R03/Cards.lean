import Apn2R03.Basic

/-! # Sizes of the ideals 2^j R (Claude, 2026-10-25) -/

set_option linter.unusedSectionVars false

namespace APN2

open Finset

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- the ideal 2^j R as a finset -/
def I (j : ℕ) : Finset R := (univ : Finset R).image (fun y => 2 ^ j * y)

theorem mem_I (j : ℕ) (x : R) : x ∈ I (R := R) j ↔ ∃ y, x = 2 ^ j * y := by
  simp only [I, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩

theorem ann_two_sub_I (j : ℕ) (hj : j ≤ S.k - 1) (w : R) (hw : 2 * w = 0) : w ∈ I (R := R) j := by
  obtain ⟨y, hy⟩ := S.tors w hw
  rw [mem_I]
  refine ⟨2 ^ (S.k - 1 - j) * y, ?_⟩
  rw [hy, ← mul_assoc, ← pow_add]
  congr 2; omega

theorem card_I_succ (hcard : Fintype.card R = Fintype.card K ^ S.k) (j : ℕ) (hj : j < S.k) :
    (I (R := R) j).card = (I (R := R) (j + 1)).card * Fintype.card K := by
  have key := Finset.card_eq_sum_card_fiberwise (s := I (R := R) j) (t := I (R := R) (j + 1))
    (f := fun x => 2 * x) (fun x hx => by
      rw [Finset.mem_coe, mem_I] at *
      obtain ⟨y, rfl⟩ := hx
      exact ⟨y, by ring⟩)
  rw [key, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro b hb
  rw [mem_I] at hb
  obtain ⟨y, rfl⟩ := hb
  rw [← S.card_ann_two hcard]
  apply Finset.card_bij (fun x _ => x - 2 ^ j * y)
  · intro x hx
    simp only [Finset.mem_filter] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_sub, hx.2]; ring
  · intro x _ x' _ h; simpa using h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨w + 2 ^ j * y, ?_, by ring⟩
    simp only [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · have hwI := S.ann_two_sub_I j (by omega) w hw
      rw [mem_I] at hwI ⊢
      obtain ⟨z, hz⟩ := hwI
      exact ⟨z + y, by rw [hz]; ring⟩
    · rw [mul_add, hw, zero_add]; ring

theorem card_I (hcard : Fintype.card R = Fintype.card K ^ S.k) :
    ∀ j, j ≤ S.k → (I (R := R) j).card = Fintype.card K ^ (S.k - j) := by
  intro j hj
  induction j with
  | zero =>
    have : I (R := R) 0 = univ := by
      ext x; simp only [mem_I, pow_zero, one_mul, Finset.mem_univ, iff_true]; exact ⟨x, rfl⟩
    rw [this, Finset.card_univ, hcard]; rfl
  | succ j ih =>
    have h1 := S.card_I_succ hcard j (by omega)
    rw [ih (by omega)] at h1
    have hq : 0 < Fintype.card K := Fintype.card_pos
    have : Fintype.card K ^ (S.k - j) = Fintype.card K ^ (S.k - (j + 1)) * Fintype.card K := by
      rw [← pow_succ]; congr 1; omega
    rw [this] at h1
    exact (Nat.eq_of_mul_eq_mul_right hq h1).symm

/-- a translate of 2^j R has q^(k-j) elements -/
theorem card_coset (hcard : Fintype.card R = Fintype.card K ^ S.k) (j : ℕ) (hj : j ≤ S.k) (b : R) :
    ((I (R := R) j).image (fun x => b + x)).card = Fintype.card K ^ (S.k - j) := by
  rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), S.card_I hcard j hj]

end GRS

end APN2

#print axioms APN2.GRS.card_I
