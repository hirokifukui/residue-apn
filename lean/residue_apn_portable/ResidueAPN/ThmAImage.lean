import ResidueAPN.Support

/-!
# Theorem 3.1(3) of paper_R5 — the image of `P' = D` is `1 + ker Tr`

`absTr m y = ∑_{i < m} y^(2^i)` is the absolute trace of `F = 𝔽_{2^m}` written as a sum of
Frobenius powers (the formula of `FiniteField.algebraMap_trace_eq_sum_pow`; the link to
`Algebra.trace` is not used here). We prove

* `absTr_frob`, `absTr_add`: the trace is additive and Frobenius-invariant;
* `card_image_evalD`: `x ↦ D(x)` takes exactly `2^(m-1)` values (it is two-to-one);
* `card_absTr_zero_le`: at most `2^(m-1)` elements have trace `0` (roots of a polynomial of degree `2^(m-1)`);
* `image_evalD`: the image of `D` is exactly `{y | Tr(y + 1) = 0} = 1 + ker Tr`.
-/

namespace ResidueAPN

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The absolute trace `Tr(y) = ∑_{i<m} y^(2^i)`. -/
def absTr (m : ℕ) (y : F) : F := ∑ i ∈ range m, y ^ (2 ^ i)

theorem absTr_add (m : ℕ) (a b : F) : absTr m (a + b) = absTr m a + absTr m b := by
  simp only [absTr, frob_add, sum_add_distrib]

theorem absTr_sq {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (y : F) : absTr m (y ^ 2) = absTr m y := by
  have h1 := sum_range_succ' (fun i => y ^ 2 ^ i) m
  rw [sum_range_succ, pow_card_two_pow hcard y, pow_zero, pow_one] at h1
  simp only [absTr]
  have : ∀ i, (y ^ 2) ^ 2 ^ i = y ^ 2 ^ (i + 1) := fun i => by rw [← pow_mul, ← pow_succ']
  simp only [this]
  exact add_right_cancel h1.symm

theorem absTr_frob {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (k : ℕ) (y : F) :
    absTr m (y ^ (2 ^ k)) = absTr m y := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, absTr_sq hcard, ih]

theorem absTr_one_add_evalD {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hr : 3 ≤ r)
    (x : F) : absTr m ((polD F m r).eval x + 1) = 0 := by
  rw [evalD_eq hcard (by omega) (by omega)]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e : 1 + (x ^ 2 ^ r + x) ^ 2 ^ (m - 2) + 1 = (x ^ 2 ^ r + x) ^ 2 ^ (m - 2) := by
    linear_combination h2
  rw [e, absTr_frob hcard, absTr_add, absTr_frob hcard, CharTwo.add_self_eq_zero]

/-- `x ↦ D(x)` takes exactly `2^(m-1)` values. -/
theorem card_image_evalD {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hr : 3 ≤ r)
    (hcop : Nat.Coprime r m) :
    (univ.image (fun x : F => (polD F m r).eval x)).card = 2 ^ (m - 1) := by
  have h := card_eq_sum_card_image (fun x : F => (polD F m r).eval x) univ
  have hfib : ∀ y ∈ univ.image (fun x : F => (polD F m r).eval x),
      (univ.filter (fun x : F => (polD F m r).eval x = y)).card = 2 := by
    intro y hy
    obtain ⟨x0, _, rfl⟩ := mem_image.mp hy
    exact evalD_fibre_card hcard hm5 hr hcop x0
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul, card_univ, hcard] at h
  have : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-- At most `2^(m-1)` elements have trace `0`. -/
theorem card_absTr_zero_le {m : ℕ} (hm : 1 ≤ m) :
    (univ.filter (fun y : F => absTr m y = 0)).card ≤ 2 ^ (m - 1) := by
  classical
  let T : F[X] := ∑ i ∈ range m, X ^ (2 ^ i)
  have hcoeff : T.coeff 1 = 1 := by
    simp only [T, finsetSum_coeff, coeff_X_pow]
    rw [sum_eq_single 0]
    · simp
    · intro i _ hi
      have : 2 ^ i ≠ 1 := by
        intro h; exact hi (Nat.pow_eq_one.mp h |>.resolve_left (by norm_num))
      simp [Ne.symm this]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  have hT0 : T ≠ 0 := by intro h; rw [h, coeff_zero] at hcoeff; exact zero_ne_one hcoeff
  have hdeg : T.natDegree ≤ 2 ^ (m - 1) := by
    refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
    rw [natDegree_X_pow]
    exact Nat.pow_le_pow_right (by norm_num) (by simp at hi; omega)
  have hsub : univ.filter (fun y : F => absTr m y = 0) ⊆ T.roots.toFinset := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and, absTr] at hy
    rw [Multiset.mem_toFinset, mem_roots hT0, IsRoot.def]
    simp only [T, eval_finsetSum, eval_pow, eval_X]
    exact hy
  calc _ ≤ T.roots.toFinset.card := card_le_card hsub
    _ ≤ Multiset.card T.roots := Multiset.toFinset_card_le _
    _ ≤ T.natDegree := card_roots' T
    _ ≤ 2 ^ (m - 1) := hdeg

/-- **Theorem 3.1(3): the image of `P' = D` is `1 + ker Tr`.** -/
theorem image_evalD {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hr : 3 ≤ r)
    (hcop : Nat.Coprime r m) :
    univ.image (fun x : F => (polD F m r).eval x) = univ.filter (fun y : F => absTr m (y + 1) = 0) := by
  have hsub : univ.image (fun x : F => (polD F m r).eval x)
      ⊆ univ.filter (fun y : F => absTr m (y + 1) = 0) := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := mem_image.mp hy
    simp only [mem_filter, mem_univ, true_and]
    exact absTr_one_add_evalD hcard hm5 hr x
  refine eq_of_subset_of_card_le hsub ?_
  rw [card_image_evalD hcard hm5 hr hcop]
  have htr : (univ.filter (fun y : F => absTr m (y + 1) = 0))
      = (univ.filter (fun y : F => absTr m y = 0)).image (fun y => y + 1) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h; refine ⟨y + 1, h, ?_⟩; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rintro ⟨z, hz, rfl⟩; rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [htr]
  exact (card_image_le).trans (card_absTr_zero_le (by omega))

end ResidueAPN
