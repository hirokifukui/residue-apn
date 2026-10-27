import Apn2R03.Layered

/-!
# Differentials (hulls) over two rounds (Claude, 2026-10-26, R05c)

Words in a finite abelian group `R`, an injective S-box `s : R → R` applied wordwise, an additive automorphism
`M` of `R^n` whose branch number over `R` (count of nonzero words) is at least `B`.
* `hull2_le` : for every nonzero input difference `a` and every `c`,
    `Σ_x DP_S(a → x) · DP_S(M x → c) ≤ p^(B−1)`,  `p = max_{u ≠ 0, v} DP_s(u → v)`.
  (For an MDS layer, `B = n + 1`: the bound `p^n`.)
-/

set_option linter.unusedSectionVars false

namespace APN2.Markov

open Finset

section hull
variable {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- word difference probability -/
noncomputable def DP (s : R → R) (u v : R) : ℚ := (dd s u v : ℚ) / Fintype.card R

/-- number of nonzero words -/
def wtG {n : ℕ} (x : Fin n → R) : ℕ := (univ.filter (fun j => x j ≠ 0)).card

theorem card_R_pos : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos

theorem DP_nonneg (s : R → R) (u v : R) : 0 ≤ DP s u v := by
  unfold DP; exact div_nonneg (Nat.cast_nonneg _) card_R_pos.le

theorem dd_eq_card_filter (s : R → R) (u v : R) :
    dd s u v = (univ.filter (fun x : R => s (x + u) - s x = v)).card := by
  unfold dd; rw [Fintype.card_subtype]

theorem DP_zero_left (s : R → R) (v : R) (hv : v ≠ 0) : DP s 0 v = 0 := by
  unfold DP
  rw [dd_eq_card_filter, Finset.card_eq_zero.mpr, Nat.cast_zero, zero_div]
  rw [Finset.filter_eq_empty_iff]
  intro x _ hx
  simp at hx
  exact hv hx.symm

theorem DP_zero_zero (s : R → R) : DP s 0 0 = 1 := by
  unfold DP
  rw [dd_eq_card_filter, Finset.filter_true_of_mem (fun x _ => by simp), Finset.card_univ]
  exact div_self card_R_pos.ne'

theorem DP_zero_right (s : R → R) (hs : Function.Injective s) (u : R) (hu : u ≠ 0) : DP s u 0 = 0 := by
  unfold DP
  rw [dd_eq_card_filter, Finset.card_eq_zero.mpr, Nat.cast_zero, zero_div]
  rw [Finset.filter_eq_empty_iff]
  intro x _ hx
  apply hu
  have := hs (sub_eq_zero.mp hx)
  simpa using this

theorem sum_DP_right (s : R → R) (u : R) : ∑ v, DP s u v = 1 := by
  unfold DP
  rw [← Finset.sum_div]
  have : ∑ v, (dd s u v : ℚ) = Fintype.card R := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset R)) (t := (univ : Finset R))
      (f := fun x : R => s (x + u) - s x) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [Finset.card_univ] at h
    rw [h]
    push_cast
    apply Finset.sum_congr rfl
    intro v _
    rw [dd_eq_card_filter]
  rw [this]; exact div_self card_R_pos.ne'

theorem sum_DP_left (s : R → R) (hs : Function.Bijective s) (v : R) : ∑ u, DP s u v = 1 := by
  unfold DP
  rw [← Finset.sum_div]
  have : ∑ u, (dd s u v : ℚ) = Fintype.card R := by
    simp only [dd_eq_card_filter, Finset.card_filter]
    push_cast
    rw [Finset.sum_comm]
    have h1 : ∀ x : R, ∑ u : R, (if s (x + u) - s x = v then (1 : ℚ) else 0) = 1 := by
      intro x
      obtain ⟨y, hy⟩ := hs.2 (s x + v)
      rw [Finset.sum_eq_single (y - x)]
      · rw [if_pos (by rw [add_sub_cancel, hy]; abel)]
      · intro u _ hu
        rw [if_neg]
        intro h
        apply hu
        have : s (x + u) = s y := by rw [hy, ← h]; abel
        have := hs.1 this
        rw [← this]; abel
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [this]; exact div_self card_R_pos.ne'

open scoped Classical in
/-- **Two-round hull bound.** -/
theorem hull2_le {n : ℕ} (s : R → R) (hs : Function.Bijective s)
    (M : (Fin n → R) ≃+ (Fin n → R)) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x))
    (p : ℚ) (hp0 : 0 ≤ p) (hp : ∀ u v : R, u ≠ 0 → DP s u v ≤ p)
    (a c : Fin n → R) (ha : a ≠ 0) :
    ∑ x : Fin n → R, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≤ p ^ (B - 1) := by
  have hDP0 : ∀ u v, DP s u v ≠ 0 → (v ≠ 0 ↔ u ≠ 0) := by
    intro u v h
    constructor
    · intro hv hu; rw [hu] at h; exact h (DP_zero_left s v hv)
    · intro hu hv; rw [hv] at h; exact h (DP_zero_right s hs.1 u hu)
  set A : Finset (Fin n) := univ.filter (fun j => a j ≠ 0) with hA
  set Bs : Finset (Fin n) := univ.filter (fun j => c j ≠ 0) with hBs
  have hsupp : ∀ x, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0 →
      (∀ j, x j ≠ 0 ↔ a j ≠ 0) ∧ (∀ j, M x j ≠ 0 ↔ c j ≠ 0) := by
    intro x hx
    have h1 := left_ne_zero_of_mul hx
    have h2 := right_ne_zero_of_mul hx
    rw [Finset.prod_ne_zero_iff] at h1 h2
    exact ⟨fun j => hDP0 _ _ (h1 j (mem_univ _)), fun j => (hDP0 _ _ (h2 j (mem_univ _))).symm⟩
  by_cases hex : ∃ x0, (∏ j, DP s (a j) (x0 j)) * (∏ j, DP s (M x0 j) (c j)) ≠ 0
  swap
  · push Not at hex
    rw [Finset.sum_eq_zero (fun x _ => hex x)]
    exact pow_nonneg hp0 _
  obtain ⟨x0, hx0⟩ := hex
  obtain ⟨hx0a, hx0c⟩ := hsupp x0 hx0
  have hx0ne : x0 ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    exact ((hx0a j).mpr hj) (by rw [h]; rfl)
  have hAB : B ≤ A.card + Bs.card := by
    have h := hB x0 hx0ne
    have e1 : wtG x0 = A.card := by
      unfold wtG; congr 1; ext j; simp only [mem_filter, mem_univ, true_and, hA]; exact hx0a j
    have e2 : wtG (M x0) = Bs.card := by
      unfold wtG; congr 1; ext j; simp only [mem_filter, mem_univ, true_and, hBs]; exact hx0c j
    omega
  obtain ⟨A', hA'A, hA'c⟩ := Finset.exists_subset_card_eq (s := A) (n := min A.card (B - 1))
    (min_le_left _ _)
  obtain ⟨B', hB'B, hB'c⟩ := Finset.exists_subset_card_eq (s := Bs) (n := B - 1 - A'.card)
    (by omega)
  have hcard' : A'.card + B'.card = B - 1 := by omega
  set Q : (Fin n → R) → ℚ := fun x =>
    (∏ j ∈ A \ A', DP s (a j) (x j)) * (∏ j ∈ Bs \ B', DP s (M x j) (c j)) with hQ
  have hQ0 : ∀ x, 0 ≤ Q x := fun x =>
    mul_nonneg (prod_nonneg fun j _ => DP_nonneg s _ _) (prod_nonneg fun j _ => DP_nonneg s _ _)
  have hbound : ∀ x, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≤ p ^ (B - 1) * Q x := by
    intro x
    by_cases hx : (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) = 0
    · rw [hx]; exact mul_nonneg (pow_nonneg hp0 _) (hQ0 x)
    obtain ⟨hxa, hxc⟩ := hsupp x hx
    have e1 : ∏ j, DP s (a j) (x j) =
        (∏ j ∈ A \ A', DP s (a j) (x j)) * ∏ j ∈ A', DP s (a j) (x j) := by
      rw [Finset.prod_sdiff hA'A]
      symm
      apply Finset.prod_subset (subset_univ _)
      intro j _ hj
      have haj : a j = 0 := by simpa [hA] using hj
      have hxj : x j = 0 := by by_contra h; exact ((hxa j).mp h) haj
      rw [haj, hxj]; exact DP_zero_zero s
    have e2 : ∏ j, DP s (M x j) (c j) =
        (∏ j ∈ Bs \ B', DP s (M x j) (c j)) * ∏ j ∈ B', DP s (M x j) (c j) := by
      rw [Finset.prod_sdiff hB'B]
      symm
      apply Finset.prod_subset (subset_univ _)
      intro j _ hj
      have hcj : c j = 0 := by simpa [hBs] using hj
      have hxj : M x j = 0 := by by_contra h; exact ((hxc j).mp h) hcj
      rw [hcj, hxj]; exact DP_zero_zero s
    have b1 : ∏ j ∈ A', DP s (a j) (x j) ≤ p ^ A'.card := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun j _ => DP_nonneg s _ _)
      intro j hj
      exact hp _ _ (by simpa [hA] using hA'A hj)
    have b2 : ∏ j ∈ B', DP s (M x j) (c j) ≤ p ^ B'.card := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun j _ => DP_nonneg s _ _)
      intro j hj
      exact hp _ _ ((hxc j).mpr (by simpa [hBs] using hB'B hj))
    have n1 : 0 ≤ ∏ j ∈ A \ A', DP s (a j) (x j) := prod_nonneg fun j _ => DP_nonneg s _ _
    have n2 : 0 ≤ ∏ j ∈ Bs \ B', DP s (M x j) (c j) := prod_nonneg fun j _ => DP_nonneg s _ _
    have n3 : 0 ≤ ∏ j ∈ A', DP s (a j) (x j) := prod_nonneg fun j _ => DP_nonneg s _ _
    have n4 : 0 ≤ ∏ j ∈ B', DP s (M x j) (c j) := prod_nonneg fun j _ => DP_nonneg s _ _
    rw [e1, e2]
    calc (∏ j ∈ A \ A', DP s (a j) (x j)) * (∏ j ∈ A', DP s (a j) (x j)) *
          ((∏ j ∈ Bs \ B', DP s (M x j) (c j)) * ∏ j ∈ B', DP s (M x j) (c j))
        ≤ (∏ j ∈ A \ A', DP s (a j) (x j)) * p ^ A'.card *
          ((∏ j ∈ Bs \ B', DP s (M x j) (c j)) * p ^ B'.card) :=
          mul_le_mul (mul_le_mul_of_nonneg_left b1 n1) (mul_le_mul_of_nonneg_left b2 n2)
            (mul_nonneg n2 n4) (mul_nonneg n1 (pow_nonneg hp0 _))
      _ = p ^ (B - 1) * Q x := by rw [hQ, ← hcard', pow_add]; ring
  -- the remaining sum is at most one
  set X := univ.filter (fun x : Fin n → R => (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0)
    with hX
  let ψ : (Fin n → R) → ((↥(A \ A') → R) × (↥(Bs \ B') → R)) := fun x => (fun j => x j, fun j => M x j)
  let Φ : ((↥(A \ A') → R) × (↥(Bs \ B') → R)) → ℚ := fun z =>
    (∏ j : ↥(A \ A'), DP s (a j) (z.1 j)) * (∏ j : ↥(Bs \ B'), DP s (z.2 j) (c j))
  have hQΦ : ∀ x, Q x = Φ (ψ x) := by
    intro x
    simp only [hQ, Φ, ψ]
    rw [Finset.prod_coe_sort (A \ A') (fun j => DP s (a j) (x j)),
      Finset.prod_coe_sort (Bs \ B') (fun j => DP s (M x j) (c j))]
  have hinj : Set.InjOn ψ X := by
    intro x hx x' hx' hψ
    simp only [hX, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hx'
    obtain ⟨hxa, hxc⟩ := hsupp x hx
    obtain ⟨hxa', hxc'⟩ := hsupp x' hx'
    have h1 := congrArg Prod.fst hψ
    have h2 := congrArg Prod.snd hψ
    by_contra hne
    have hd : x - x' ≠ 0 := sub_ne_zero.mpr hne
    have h := hB (x - x') hd
    have w1 : wtG (x - x') ≤ A'.card := by
      unfold wtG
      apply Finset.card_le_card
      intro j hj
      simp only [mem_filter, mem_univ, true_and, Pi.sub_apply] at hj
      by_contra hjA'
      by_cases hjA : j ∈ A
      · have := congrFun h1 ⟨j, mem_sdiff.mpr ⟨hjA, hjA'⟩⟩
        exact hj (sub_eq_zero.mpr this)
      · have haj : a j = 0 := by simpa [hA] using hjA
        have e : x j = 0 := by by_contra h; exact ((hxa j).mp h) haj
        have e' : x' j = 0 := by by_contra h; exact ((hxa' j).mp h) haj
        exact hj (by rw [e, e', sub_zero])
    have w2 : wtG (M (x - x')) ≤ B'.card := by
      unfold wtG
      apply Finset.card_le_card
      intro j hj
      simp only [mem_filter, mem_univ, true_and, map_sub, Pi.sub_apply] at hj
      by_contra hjB'
      by_cases hjB : j ∈ Bs
      · have := congrFun h2 ⟨j, mem_sdiff.mpr ⟨hjB, hjB'⟩⟩
        exact hj (sub_eq_zero.mpr this)
      · have hcj : c j = 0 := by simpa [hBs] using hjB
        have e : M x j = 0 := by by_contra h; exact ((hxc j).mp h) hcj
        have e' : M x' j = 0 := by by_contra h; exact ((hxc' j).mp h) hcj
        exact hj (by rw [e, e', sub_zero])
    omega
  have hΦ0 : ∀ z, 0 ≤ Φ z := fun z =>
    mul_nonneg (prod_nonneg fun j _ => DP_nonneg s _ _) (prod_nonneg fun j _ => DP_nonneg s _ _)
  have hsum1 : ∑ x ∈ X, Q x ≤ 1 := by
    calc ∑ x ∈ X, Q x = ∑ x ∈ X, Φ (ψ x) := Finset.sum_congr rfl (fun x _ => hQΦ x)
      _ = ∑ z ∈ X.image ψ, Φ z := (Finset.sum_image (fun x hx x' hx' h => hinj hx hx' h)).symm
      _ ≤ ∑ z, Φ z := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z _ _ => hΦ0 z)
      _ = (∑ z1 : ↥(A \ A') → R, ∏ j : ↥(A \ A'), DP s (a j) (z1 j)) *
          (∑ z2 : ↥(Bs \ B') → R, ∏ j : ↥(Bs \ B'), DP s (z2 j) (c j)) := by
          rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ = 1 := by
          have e1 : (∑ z1 : ↥(A \ A') → R, ∏ j : ↥(A \ A'), DP s (a j) (z1 j)) = 1 := by
            rw [← Fintype.prod_sum]
            simp only [sum_DP_right, prod_const_one]
          have e2 : (∑ z2 : ↥(Bs \ B') → R, ∏ j : ↥(Bs \ B'), DP s (z2 j) (c j)) = 1 := by
            rw [← Fintype.prod_sum (fun (j : ↥(Bs \ B')) (t : R) => DP s t (c j))]
            simp only [sum_DP_left s hs, prod_const_one]
          rw [e1, e2, mul_one]
  calc ∑ x, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j))
      = ∑ x ∈ X, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) := by
        rw [hX, Finset.sum_filter_ne_zero]
    _ ≤ ∑ x ∈ X, p ^ (B - 1) * Q x := Finset.sum_le_sum (fun x _ => hbound x)
    _ = p ^ (B - 1) * ∑ x ∈ X, Q x := by rw [Finset.mul_sum]
    _ ≤ p ^ (B - 1) * 1 := mul_le_mul_of_nonneg_left hsum1 (pow_nonneg hp0 _)
    _ = p ^ (B - 1) := mul_one _

end hull

end APN2.Markov

#print axioms APN2.Markov.hull2_le
