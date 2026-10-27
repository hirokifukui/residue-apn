import Mathlib

/-!
# APN2 — abstract Galois-ring setting (Claude, 2026-10-25)

`GRS R F` axiomatizes GR(2^k, m) with residue field F = F_q:
* `π : R →+* F` surjective with kernel `2R`,
* `2^k = 0` in `R`,
* the 2-torsion of `R` is exactly `2^(k-1) R`,
* `|R| = q^k`.
These hold for GR(2^k, m).  Everything below is proved from these axioms only.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset

structure GRS (R F : Type*) [CommRing R] [Field F] where
  π : R →+* F
  surj : Function.Surjective π
  k : ℕ
  hk : 3 ≤ k
  ker2 : ∀ x : R, π x = 0 ↔ ∃ y, x = 2 * y
  nil : (2 : R) ^ k = 0
  tors : ∀ x : R, 2 * x = 0 → ∃ y, x = 2 ^ (k - 1) * y

namespace GRS

variable {R F : Type*} [CommRing R] [Field F] (S : GRS R F)

theorem pi_two : S.π 2 = 0 := (S.ker2 2).mpr ⟨1, by ring⟩

theorem pi_two_mul (y : R) : S.π (2 * y) = 0 := by
  rw [map_mul, S.pi_two, zero_mul]

theorem pi_two_pow_mul (j : ℕ) (hj : 1 ≤ j) (y : R) : S.π (2 ^ j * y) = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [pow_succ, mul_comm ((2 : R) ^ i) 2, mul_assoc]
  exact S.pi_two_mul _

/-- annihilator of `2^j` is `2^d R` when `j + d = k`. -/
theorem ann_two_pow : ∀ (j d : ℕ), j + d = S.k → ∀ x : R, 2 ^ j * x = 0 → ∃ y, x = 2 ^ d * y := by
  intro j
  induction j with
  | zero =>
    intro d hd x hx
    exact ⟨0, by simpa using hx⟩
  | succ j ih =>
    intro d hd x hx
    have h1 : 2 ^ j * (2 * x) = 0 := by rw [← hx]; ring
    obtain ⟨y, hy⟩ := ih (d + 1) (by omega) (2 * x) h1
    have h2 : 2 * (x - 2 ^ d * y) = 0 := by rw [mul_sub, hy]; ring
    obtain ⟨z, hz⟩ := S.tors _ h2
    have hk1 : S.k - 1 = j + d := by omega
    refine ⟨y + 2 ^ j * z, ?_⟩
    rw [hk1] at hz
    have : x = 2 ^ d * y + 2 ^ (j + d) * z := by rw [← hz]; ring
    rw [this]; ring

theorem pi_eq_of_two_mul_eq {y y' : R} (h : 2 * y = 2 * y') : S.π y = S.π y' := by
  have h0 : 2 ^ 1 * (y - y') = 0 := by rw [pow_one, mul_sub, h, sub_self]
  obtain ⟨z, hz⟩ := S.ann_two_pow 1 (S.k - 1) (by have := S.hk; omega) _ h0
  have : S.π (y - y') = 0 := by
    rw [hz]; exact S.pi_two_pow_mul _ (by have := S.hk; omega) _
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem pi_eq_of_four_mul_eq {y y' : R} (h : 4 * y = 4 * y') : S.π y = S.π y' := by
  have h0 : 2 ^ 2 * (y - y') = 0 := by
    rw [mul_sub]; norm_num; rw [h, sub_self]
  obtain ⟨z, hz⟩ := S.ann_two_pow 2 (S.k - 2) (by have := S.hk; omega) _ h0
  have : S.π (y - y') = 0 := by
    rw [hz]; exact S.pi_two_pow_mul _ (by have := S.hk; omega) _
  rw [map_sub, sub_eq_zero] at this
  exact this

/-- residue of `x / 2` (meaningful when `x ∈ 2R`). -/
noncomputable def half (x : R) : F :=
  by classical exact if h : ∃ y, x = 2 * y then S.π h.choose else 0

/-- residue of `x / 4` (meaningful when `x ∈ 4R`). -/
noncomputable def quarter (x : R) : F :=
  by classical exact if h : ∃ y, x = 4 * y then S.π h.choose else 0

theorem half_eq (y : R) : S.half (2 * y) = S.π y := by
  classical
  have h : ∃ y', 2 * y = 2 * y' := ⟨y, rfl⟩
  unfold half
  rw [dif_pos h]
  exact S.pi_eq_of_two_mul_eq h.choose_spec.symm

theorem quarter_eq (y : R) : S.quarter (4 * y) = S.π y := by
  classical
  have h : ∃ y', 4 * y = 4 * y' := ⟨y, rfl⟩
  unfold quarter
  rw [dif_pos h]
  exact S.pi_eq_of_four_mul_eq h.choose_spec.symm

/-- `2^j y ∈ 2^(j+1) R ↔ π y = 0` for `j < k`. -/
theorem two_pow_mul_mem_iff (j : ℕ) (hj : j < S.k) (y : R) :
    (∃ w, 2 ^ j * y = 2 ^ (j + 1) * w) ↔ S.π y = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    have h0 : 2 ^ j * (y - 2 * w) = 0 := by rw [mul_sub, hw]; ring
    obtain ⟨z, hz⟩ := S.ann_two_pow j (S.k - j) (by omega) _ h0
    have : S.π (y - 2 * w) = 0 := by rw [hz]; exact S.pi_two_pow_mul _ (by omega) _
    rw [map_sub, S.pi_two_mul, sub_zero] at this
    exact this
  · intro h
    obtain ⟨w, hw⟩ := (S.ker2 y).mp h
    exact ⟨w, by rw [hw]; ring⟩

/-- `x ∈ 2^j R` membership helper: `4 * P = 0 ↔ P ∈ 2^(k-2) R`. -/
theorem four_mul_eq_zero_iff (P : R) : 4 * P = 0 ↔ ∃ w, P = 2 ^ (S.k - 2) * w := by
  constructor
  · intro h
    have h' : 2 ^ 2 * P = 0 := by rw [← h]; norm_num
    exact S.ann_two_pow 2 (S.k - 2) (by have := S.hk; omega) P h'
  · rintro ⟨w, rfl⟩
    have : (4 : R) * (2 ^ (S.k - 2) * w) = 2 ^ S.k * w := by
      rw [show (4 : R) = 2 ^ 2 by norm_num, ← mul_assoc, ← pow_add]
      congr 2; have := S.hk; omega
    rw [this, S.nil, zero_mul]

section card
variable [Fintype R] [DecidableEq R] [Fintype F] [DecidableEq F]

/-- all residue fibers have the same size -/
theorem card_fiber_eq (a b : F) :
    (univ.filter (fun x : R => S.π x = a)).card = (univ.filter (fun x : R => S.π x = b)).card := by
  obtain ⟨xa, hxa⟩ := S.surj a
  obtain ⟨xb, hxb⟩ := S.surj b
  apply Finset.card_bij (fun x _ => x - xa + xb)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [map_add, map_sub, hx, hxa, hxb]; ring
  · intro x _ y _ h
    simpa using h
  · intro y hy
    refine ⟨y - xb + xa, ?_, by ring⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [map_add, map_sub, hy, hxa, hxb]; ring

theorem card_fiber (hcard : Fintype.card R = Fintype.card F ^ S.k) (a : F) :
    (univ.filter (fun x : R => S.π x = a)).card = Fintype.card F ^ (S.k - 1) := by
  have key := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset R)) (t := (univ : Finset F))
    (f := fun x => S.π x) (fun x _ => Finset.mem_univ _)
  have hconst : ∀ b ∈ (univ : Finset F),
      (univ.filter (fun x : R => S.π x = b)).card = (univ.filter (fun x : R => S.π x = a)).card :=
    fun b _ => S.card_fiber_eq b a
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Finset.card_univ, hcard] at key
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hk := S.hk
  have : Fintype.card F ^ S.k = Fintype.card F * Fintype.card F ^ (S.k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [this] at key
  exact (Nat.eq_of_mul_eq_mul_left hq key).symm

/-- the 2-torsion has exactly q elements -/
theorem card_ann_two (hcard : Fintype.card R = Fintype.card F ^ S.k) :
    (univ.filter (fun z : R => 2 * z = 0)).card = Fintype.card F := by
  -- fibers of z ↦ 2z over its image (= ker π) all have the size of ann(2)
  have key := Finset.card_eq_sum_card_image (fun z : R => 2 * z) (univ : Finset R)
  have himg : (univ : Finset R).image (fun z : R => 2 * z) = univ.filter (fun x : R => S.π x = 0) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    rw [S.ker2 x]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  have hfib : ∀ b ∈ (univ : Finset R).image (fun z : R => 2 * z),
      (univ.filter (fun z : R => 2 * z = b)).card = (univ.filter (fun z : R => 2 * z = 0)).card := by
    intro b hb
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.card_bij (fun z _ => z - y)
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [mul_sub, hz, sub_self]
    · intro z _ w _ h; simpa using h
    · intro w hw
      refine ⟨w + y, ?_, by ring⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [mul_add, hw, zero_add]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, himg, S.card_fiber hcard 0,
    Finset.card_univ, hcard] at key
  have hq : 0 < Fintype.card F ^ (S.k - 1) := pow_pos Fintype.card_pos _
  have hk := S.hk
  have : Fintype.card F ^ S.k = Fintype.card F ^ (S.k - 1) * Fintype.card F := by
    rw [← pow_succ]; congr 1; omega
  rw [this] at key
  exact (Nat.eq_of_mul_eq_mul_left hq key).symm

end card

end GRS

/-- Non-vacuity: `ZMod 8` over `ZMod 2` satisfies the axioms (m = 1, k = 3). -/
def zmod8 : GRS (ZMod 8) (ZMod 2) where
  π := ZMod.castHom (by norm_num) (ZMod 2)
  surj := ZMod.ringHom_surjective _
  k := 3
  hk := le_refl 3
  ker2 := by decide
  nil := by decide
  tors := by decide

end APN2

#print axioms APN2.GRS.card_fiber
#print axioms APN2.GRS.card_ann_two
#print axioms APN2.GRS.quarter_eq
#print axioms APN2.GRS.two_pow_mul_mem_iff
#print axioms APN2.zmod8
