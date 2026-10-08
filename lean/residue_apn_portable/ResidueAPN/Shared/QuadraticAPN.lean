-- Copied from ~/lean/apnlift/APNLift/Core/QuadraticAPN.lean (apnlift, H. Fukui; sha256 2a9a96541d2db4c7…)
-- on 2026-10-07; only the namespace APNLift -> ResidueAPN and the import path were changed.
import ResidueAPN.Shared.Definitions

/-!
# Quadratic functions, derivatives, APN

Specification entry S2.

Characteristic two enters here and not before.  `polar` is written with `+` throughout, which is
only the polar form in characteristic two; every result in this file carries `[CharP F 2]`.

Note what is *not* done here: the correspondence between `IsQuadratic` (the polar form is
additive) and Boolean degree at most two is a separate obligation, and nothing below assumes it.
-/

namespace ResidueAPN

variable {F : Type*} [Field F] [CharP F 2]

/-- The derivative of `Q` in direction `a`. -/
def deriv (Q : F → F) (a x : F) : F := Q (x + a) + Q x

/-- The derivative is the polar form shifted by a constant.  This is the whole reason the
polar form controls the differential behaviour. -/
theorem deriv_eq_polar_add (Q : F → F) (a x : F) :
    deriv Q a x = polar Q a x + (Q a + Q 0) := by
  have key : ∀ A B C D : F, A + B + C + D + (B + D) = A + C := by
    intro A B C D
    have h : A + B + C + D + (B + D) = A + C + (B + B) + (D + D) := by abel
    rw [h, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, add_zero]
  unfold deriv polar
  rw [add_comm x a]
  exact (key _ _ _ _).symm

/-- For a quadratic `Q`, two points have the same derivative value exactly when their sum is in
the kernel of the polar form.  The fibres of the derivative are therefore the cosets of that
kernel. -/
theorem deriv_eq_iff (Q : F → F) (hQ : IsQuadratic Q) (a x y : F) :
    deriv Q a x = deriv Q a y ↔ polar Q a (x + y) = 0 := by
  rw [deriv_eq_polar_add, deriv_eq_polar_add, add_right_cancel_iff, hQ a x y]
  exact CharTwo.add_eq_zero.symm

section Counting

variable [Fintype F] [DecidableEq F]

/-- The kernel of the polar form in direction `a`. -/
def polarKer (Q : F → F) (a : F) : Finset F :=
  Finset.univ.filter (fun x : F => polar Q a x = 0)

/-- `Q` is APN: in every nonzero direction the derivative is at most two-to-one. -/
def IsAPN (Q : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    (Finset.univ.filter (fun x : F => deriv Q a x = b)).card ≤ 2

/-- For a quadratic function, APN forces the polar kernel to have at most two elements.
The kernel is literally one of the fibres, the one through `0`. -/
theorem polarKer_card_le_of_isAPN {Q : F → F} (hQ : IsQuadratic Q) (hAPN : IsAPN Q)
    {a : F} (ha : a ≠ 0) : (polarKer Q a).card ≤ 2 := by
  have himg : polarKer Q a
      = Finset.univ.filter (fun x : F => deriv Q a x = deriv Q a 0) := by
    unfold polarKer
    apply Finset.filter_congr
    intro x _
    rw [deriv_eq_iff Q hQ a x 0, add_zero]
  rw [himg]
  exact hAPN a ha (deriv Q a 0)

end Counting

section Kernel

/-- The polar form vanishes at `0`. -/
theorem polar_zero_right (Q : F → F) (a : F) : polar Q a 0 = 0 := by
  have h : Q (a + 0) + Q a + Q 0 + Q 0 = (Q a + Q a) + (Q 0 + Q 0) := by
    rw [add_zero]; abel
  unfold polar
  rw [h, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

/-- The polar form vanishes at the direction itself: `a` is always in the kernel. -/
theorem polar_self (Q : F → F) (a : F) : polar Q a a = 0 := by
  have h : Q (a + a) + Q a + Q a + Q 0 = (Q (a + a) + Q 0) + (Q a + Q a) := by abel
  unfold polar
  rw [h, CharTwo.add_self_eq_zero (x := a), CharTwo.add_self_eq_zero (x := Q a), add_zero,
    CharTwo.add_self_eq_zero]

end Kernel

section KernelPair

variable [Fintype F] [DecidableEq F]

/-- `{0, a}` always sits inside the polar kernel. -/
theorem pair_subset_polarKer (Q : F → F) (a : F) : ({0, a} : Finset F) ⊆ polarKer Q a := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  . simp [polarKer, polar_zero_right]
  . rw [Finset.mem_singleton] at hx
    subst hx
    simp [polarKer, polar_self]

/-- **For a quadratic APN function the polar kernel is exactly `{0, a}`.**
The upper bound comes from APN, the lower bound from the two elements that are always there;
they meet. -/
theorem polarKer_eq_pair {Q : F → F} (hQ : IsQuadratic Q) (hAPN : IsAPN Q)
    {a : F} (ha : a ≠ 0) : polarKer Q a = ({0, a} : Finset F) := by
  refine (Finset.eq_of_subset_of_card_le (pair_subset_polarKer Q a) ?_).symm
  rw [Finset.card_pair (Ne.symm ha)]
  exact polarKer_card_le_of_isAPN hQ hAPN ha

/-- Consequently the kernel has exactly two elements. -/
theorem polarKer_card {Q : F → F} (hQ : IsQuadratic Q) (hAPN : IsAPN Q)
    {a : F} (ha : a ≠ 0) : (polarKer Q a).card = 2 := by
  rw [polarKer_eq_pair hQ hAPN ha, Finset.card_pair (Ne.symm ha)]

/-- The derivative of a quadratic APN function is exactly two-to-one: `deriv Q a x = deriv Q a y`
forces `y = x` or `y = x + a`, and both really occur. -/
theorem deriv_eq_iff_pair {Q : F → F} (hQ : IsQuadratic Q) (hAPN : IsAPN Q)
    {a : F} (ha : a ≠ 0) (x y : F) :
    deriv Q a x = deriv Q a y ↔ (y = x ∨ y = x + a) := by
  rw [deriv_eq_iff Q hQ a x y]
  constructor
  . intro h
    have hx : x + y ∈ polarKer Q a := by simp [polarKer, h]
    rw [polarKer_eq_pair hQ hAPN ha] at hx
    rcases Finset.mem_insert.mp hx with h0 | h1
    . exact Or.inl (CharTwo.add_eq_zero.mp h0).symm
    . rw [Finset.mem_singleton] at h1
      refine Or.inr ?_
      have h2 : x + (x + y) = x + a := by rw [h1]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h2
      exact h2
  . rintro (rfl | rfl)
    . rw [CharTwo.add_self_eq_zero]
      exact polar_zero_right Q a
    . rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      exact polar_self Q a

/-- **Converse of `polarKer_card_le_of_isAPN`.**  For a quadratic function, a polar kernel of at
most two elements forces APN.  Every nonempty fibre of the derivative is a translate of the
kernel, so the two have the same size. -/
theorem isAPN_of_polarKer_card {Q : F → F} (hQ : IsQuadratic Q)
    (h : ∀ a : F, a ≠ 0 → (polarKer Q a).card ≤ 2) : IsAPN Q := by
  intro a ha b
  by_cases hemp : (Finset.univ.filter (fun x : F => deriv Q a x = b)).Nonempty
  . obtain ⟨x0, hx0mem⟩ := hemp
    have hx0 : deriv Q a x0 = b := (Finset.mem_filter.mp hx0mem).2
    have himg : (Finset.univ.filter (fun x : F => deriv Q a x = b)).image (fun x => x + x0)
        = polarKer Q a := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, polarKer]
      constructor
      . rintro ⟨x, hx, rfl⟩
        exact (deriv_eq_iff Q hQ a x x0).mp (by rw [hx, hx0])
      . intro hy
        refine ⟨y + x0, ?_, ?_⟩
        . have hcancel : y + x0 + x0 = y := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
          have := (deriv_eq_iff Q hQ a (y + x0) x0).mpr (by rw [hcancel]; exact hy)
          rw [this, hx0]
        . rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hcard : (Finset.univ.filter (fun x : F => deriv Q a x = b)).card
        = (polarKer Q a).card := by
      rw [← himg, Finset.card_image_of_injective _ (add_left_injective x0)]
    rw [hcard]
    exact h a ha
  . rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [hemp]

/-- For quadratic functions, APN is exactly the two-element polar kernel condition. -/
theorem isAPN_iff_polarKer_card {Q : F → F} (hQ : IsQuadratic Q) :
    IsAPN Q ↔ ∀ a : F, a ≠ 0 → (polarKer Q a).card ≤ 2 :=
  ⟨fun hAPN a ha => polarKer_card_le_of_isAPN hQ hAPN ha,
    fun h => isAPN_of_polarKer_card hQ h⟩

end KernelPair

end ResidueAPN
