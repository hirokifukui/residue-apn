import Apn2R03.HullFam

/-!
# Differentials with a unit input component: a lift-dependent bound (Claude, 2026-10-26, R05c)

* `hull_core`  : the two-round sum over any set `Y` of first-round outputs is `≤ p^(B−1)` once `B − 1`
                 factors (input words in `A'`, output words in `C'`) are bounded by `p` on `Y`;
* `hull2_unit` : if every contributing `x` has at least `B` "unit" words in `a` and `M x` together, and unit
                 rows are bounded by `p_u`, the two-round sum is `≤ 2^n p_u^(B−1)` (split by the unit pattern of `M x`);
* `fam5_diff2_unit` : for `F♯` (`r ≥ 5`) and an input difference with a unit word, every two-round differential has
                 probability `≤ 2^n (2q/q^k)^(B−1)`; `fam5_fixed_key_unit` is the fixed-key form.
-/

set_option linter.unusedSectionVars false

namespace APN2.Markov

open Finset

section core
variable {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]

open scoped Classical in
theorem hull_core {n : ℕ} (s : R → R) (hs : Function.Bijective s)
    (M : (Fin n → R) ≃+ (Fin n → R)) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x))
    (p : ℚ) (hp0 : 0 ≤ p) (a c : Fin n → R) (Y : Finset (Fin n → R)) (A' C' : Finset (Fin n))
    (hA' : ∀ j ∈ A', a j ≠ 0) (hC' : ∀ j ∈ C', c j ≠ 0) (hcard : A'.card + C'.card = B - 1)
    (hpA : ∀ x ∈ Y, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0 →
      ∀ j ∈ A', DP s (a j) (x j) ≤ p)
    (hpC : ∀ x ∈ Y, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0 →
      ∀ j ∈ C', DP s (M x j) (c j) ≤ p) :
    ∑ x ∈ Y, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≤ p ^ (B - 1) := by
  have hDP0 : ∀ u v, DP s u v ≠ 0 → (v ≠ 0 ↔ u ≠ 0) := by
    intro u v h
    constructor
    · intro hv hu; rw [hu] at h; exact h (DP_zero_left s v hv)
    · intro hu hv; rw [hv] at h; exact h (DP_zero_right s hs.1 u hu)
  set A : Finset (Fin n) := univ.filter (fun j => a j ≠ 0) with hA
  set Cs : Finset (Fin n) := univ.filter (fun j => c j ≠ 0) with hCs
  have hA'A : A' ⊆ A := fun j hj => by simp [hA, hA' j hj]
  have hC'C : C' ⊆ Cs := fun j hj => by simp [hCs, hC' j hj]
  have hsupp : ∀ x, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0 →
      (∀ j, x j ≠ 0 ↔ a j ≠ 0) ∧ (∀ j, M x j ≠ 0 ↔ c j ≠ 0) := by
    intro x hx
    have h1 := left_ne_zero_of_mul hx
    have h2 := right_ne_zero_of_mul hx
    rw [Finset.prod_ne_zero_iff] at h1 h2
    exact ⟨fun j => hDP0 _ _ (h1 j (mem_univ _)), fun j => (hDP0 _ _ (h2 j (mem_univ _))).symm⟩
  set Q : (Fin n → R) → ℚ := fun x =>
    (∏ j ∈ A \ A', DP s (a j) (x j)) * (∏ j ∈ Cs \ C', DP s (M x j) (c j)) with hQ
  have hQ0 : ∀ x, 0 ≤ Q x := fun x =>
    mul_nonneg (prod_nonneg fun j _ => DP_nonneg s _ _) (prod_nonneg fun j _ => DP_nonneg s _ _)
  have hbound : ∀ x ∈ Y, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≤ p ^ (B - 1) * Q x := by
    intro x hxY
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
        (∏ j ∈ Cs \ C', DP s (M x j) (c j)) * ∏ j ∈ C', DP s (M x j) (c j) := by
      rw [Finset.prod_sdiff hC'C]
      symm
      apply Finset.prod_subset (subset_univ _)
      intro j _ hj
      have hcj : c j = 0 := by simpa [hCs] using hj
      have hxj : M x j = 0 := by by_contra h; exact ((hxc j).mp h) hcj
      rw [hcj, hxj]; exact DP_zero_zero s
    have b1 : ∏ j ∈ A', DP s (a j) (x j) ≤ p ^ A'.card := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun j _ => DP_nonneg s _ _) (hpA x hxY hx)
    have b2 : ∏ j ∈ C', DP s (M x j) (c j) ≤ p ^ C'.card := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun j _ => DP_nonneg s _ _) (hpC x hxY hx)
    have n1 : 0 ≤ ∏ j ∈ A \ A', DP s (a j) (x j) := prod_nonneg fun j _ => DP_nonneg s _ _
    have n2 : 0 ≤ ∏ j ∈ Cs \ C', DP s (M x j) (c j) := prod_nonneg fun j _ => DP_nonneg s _ _
    have n4 : 0 ≤ ∏ j ∈ C', DP s (M x j) (c j) := prod_nonneg fun j _ => DP_nonneg s _ _
    rw [e1, e2]
    calc (∏ j ∈ A \ A', DP s (a j) (x j)) * (∏ j ∈ A', DP s (a j) (x j)) *
          ((∏ j ∈ Cs \ C', DP s (M x j) (c j)) * ∏ j ∈ C', DP s (M x j) (c j))
        ≤ (∏ j ∈ A \ A', DP s (a j) (x j)) * p ^ A'.card *
          ((∏ j ∈ Cs \ C', DP s (M x j) (c j)) * p ^ C'.card) :=
          mul_le_mul (mul_le_mul_of_nonneg_left b1 n1) (mul_le_mul_of_nonneg_left b2 n2)
            (mul_nonneg n2 n4) (mul_nonneg n1 (pow_nonneg hp0 _))
      _ = p ^ (B - 1) * Q x := by rw [hQ, ← hcard, pow_add]; ring
  set X := Y.filter (fun x : Fin n → R => (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0)
    with hX
  let ψ : (Fin n → R) → ((↥(A \ A') → R) × (↥(Cs \ C') → R)) := fun x => (fun j => x j, fun j => M x j)
  let Φ : ((↥(A \ A') → R) × (↥(Cs \ C') → R)) → ℚ := fun z =>
    (∏ j : ↥(A \ A'), DP s (a j) (z.1 j)) * (∏ j : ↥(Cs \ C'), DP s (z.2 j) (c j))
  have hQΦ : ∀ x, Q x = Φ (ψ x) := by
    intro x
    simp only [hQ, Φ, ψ]
    rw [Finset.prod_coe_sort (A \ A') (fun j => DP s (a j) (x j)),
      Finset.prod_coe_sort (Cs \ C') (fun j => DP s (M x j) (c j))]
  have hinj : Set.InjOn ψ X := by
    intro x hx x' hx' hψ
    simp only [hX, coe_filter, Set.mem_setOf_eq] at hx hx'
    obtain ⟨hxa, hxc⟩ := hsupp x hx.2
    obtain ⟨hxa', hxc'⟩ := hsupp x' hx'.2
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
    have w2 : wtG (M (x - x')) ≤ C'.card := by
      unfold wtG
      apply Finset.card_le_card
      intro j hj
      simp only [mem_filter, mem_univ, true_and, map_sub, Pi.sub_apply] at hj
      by_contra hjC'
      by_cases hjC : j ∈ Cs
      · have := congrFun h2 ⟨j, mem_sdiff.mpr ⟨hjC, hjC'⟩⟩
        exact hj (sub_eq_zero.mpr this)
      · have hcj : c j = 0 := by simpa [hCs] using hjC
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
          (∑ z2 : ↥(Cs \ C') → R, ∏ j : ↥(Cs \ C'), DP s (z2 j) (c j)) := by
          rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ = 1 := by
          have e1 : (∑ z1 : ↥(A \ A') → R, ∏ j : ↥(A \ A'), DP s (a j) (z1 j)) = 1 := by
            rw [← Fintype.prod_sum]
            simp only [sum_DP_right, prod_const_one]
          have e2 : (∑ z2 : ↥(Cs \ C') → R, ∏ j : ↥(Cs \ C'), DP s (z2 j) (c j)) = 1 := by
            rw [← Fintype.prod_sum (fun (j : ↥(Cs \ C')) (t : R) => DP s t (c j))]
            simp only [sum_DP_left s hs, prod_const_one]
          rw [e1, e2, mul_one]
  calc ∑ x ∈ Y, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j))
      = ∑ x ∈ X, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) := by
        rw [hX, Finset.sum_filter_ne_zero]
    _ ≤ ∑ x ∈ X, p ^ (B - 1) * Q x :=
        Finset.sum_le_sum (fun x hx => hbound x (Finset.mem_filter.mp hx).1)
    _ = p ^ (B - 1) * ∑ x ∈ X, Q x := by rw [Finset.mul_sum]
    _ ≤ p ^ (B - 1) * 1 := mul_le_mul_of_nonneg_left hsum1 (pow_nonneg hp0 _)
    _ = p ^ (B - 1) := mul_one _

open scoped Classical in
/-- **Unit-input differentials**: split by the unit pattern of `M x`. -/
theorem hull2_unit {n : ℕ} (s : R → R) (hs : Function.Bijective s)
    (M : (Fin n → R) ≃+ (Fin n → R)) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x))
    (U : R → Prop) (hU0 : ∀ u, U u → u ≠ 0)
    (pu : ℚ) (hpu0 : 0 ≤ pu) (hpu : ∀ u v : R, U u → DP s u v ≤ pu) (a c : Fin n → R)
    (hres : ∀ x, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0 →
      B ≤ (univ.filter (fun j => U (a j))).card + (univ.filter (fun j => U (M x j))).card) :
    ∑ x : Fin n → R, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≤ 2 ^ n * pu ^ (B - 1) := by
  set term : (Fin n → R) → ℚ := fun x => (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) with hterm
  set pat : (Fin n → R) → Finset (Fin n) := fun x => univ.filter (fun j => U (M x j)) with hpat
  set Ua : Finset (Fin n) := univ.filter (fun j => U (a j)) with hUa
  have hDP0 : ∀ u v, DP s u v ≠ 0 → (v ≠ 0 ↔ u ≠ 0) := by
    intro u v h
    constructor
    · intro hv hu; rw [hu] at h; exact h (DP_zero_left s v hv)
    · intro hu hv; rw [hv] at h; exact h (DP_zero_right s hs.1 u hu)
  rw [← Finset.sum_fiberwise univ pat term]
  have hP : ∀ P : Finset (Fin n), ∑ x ∈ univ.filter (fun x => pat x = P), term x ≤ pu ^ (B - 1) := by
    intro P
    by_cases hex : ∃ x ∈ univ.filter (fun x => pat x = P), term x ≠ 0
    · obtain ⟨x0, hx0P, hx0⟩ := hex
      have hpx0 : pat x0 = P := (Finset.mem_filter.mp hx0P).2
      have hcnt := hres x0 hx0
      have hPc : ∀ j ∈ P, c j ≠ 0 := by
        intro j hj
        rw [← hpx0] at hj
        have hU := (Finset.mem_filter.mp hj).2
        have h2 := right_ne_zero_of_mul hx0
        rw [Finset.prod_ne_zero_iff] at h2
        exact (hDP0 _ _ (h2 j (mem_univ _))).mpr (hU0 _ hU)
      have hcnt' : B ≤ Ua.card + (pat x0).card := hcnt
      rw [← hpx0]
      obtain ⟨A', hA'A, hA'c⟩ := Finset.exists_subset_card_eq (s := Ua) (n := min Ua.card (B - 1))
        (min_le_left _ _)
      obtain ⟨C', hC'P, hC'c⟩ := Finset.exists_subset_card_eq (s := pat x0) (n := B - 1 - A'.card)
        (by omega)
      apply hull_core s hs M B hB1 hB pu hpu0 a c _ A' C'
        (fun j hj => hU0 _ (Finset.mem_filter.mp (hA'A hj)).2)
        (fun j hj => hPc j (hpx0 ▸ hC'P hj)) (by omega)
      · intro x _ _ j hj
        exact hpu _ _ (Finset.mem_filter.mp (hA'A hj)).2
      · intro x hx _ j hj
        have hpx : pat x = pat x0 := (Finset.mem_filter.mp hx).2
        have : j ∈ pat x := by rw [hpx]; exact hC'P hj
        exact hpu _ _ (Finset.mem_filter.mp this).2
    · push Not at hex
      rw [Finset.sum_eq_zero hex]
      exact pow_nonneg hpu0 _
  calc ∑ P : Finset (Fin n), ∑ x ∈ univ.filter (fun x => pat x = P), term x
      ≤ ∑ _P : Finset (Fin n), pu ^ (B - 1) := Finset.sum_le_sum (fun P _ => hP P)
    _ = 2 ^ n * pu ^ (B - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

open scoped Classical in
theorem diff2_unit_le {n : ℕ} (s : R → R) (hs : Function.Bijective s)
    (M : (Fin n → R) ≃+ (Fin n → R)) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x))
    (U : R → Prop) (hU0 : ∀ u, U u → u ≠ 0)
    (pu : ℚ) (hpu0 : 0 ≤ pu) (hpu : ∀ u v : R, U u → DP s u v ≤ pu) (a b : Fin n → R)
    (hres : ∀ x, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (M.symm b j)) ≠ 0 →
      B ≤ (univ.filter (fun j => U (a j))).card + (univ.filter (fun j => U (M x j))).card) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => s (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤ 2 ^ n * pu ^ (B - 1) := by
  rw [prob_out2]
  simp only [dd_word]
  exact hull2_unit s hs M B hB1 hB U hU0 pu hpu0 hpu a (M.symm b) hres

end core

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- **Two-round differentials with a unit input component, `F♯` (`r ≥ 5`)**: `≤ 2^n (2q/q^k)^(B−1)`. -/
theorem fam5_diff2_unit (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (a b : Fin n → R) (ha : ∃ j, S0.π (a j) ≠ 0) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤
      2 ^ n * (((2 * Fintype.card K : ℕ) : ℚ) / Fintype.card R) ^ (B - 1) := by
  haveI := S0.charP2
  have hinj : Function.Injective (fun t : K => ((APN2.Fsh5 R m r).map S0.π).eval t) := by
    rw [S0.fam5_sh_map m r]; exact resPerm5 m r hm5 hr5 hmodd hm hcop hodd
  apply diff2_unit_le (fun x : R => (APN2.Fsh5 R m r).eval x) (S0.fam5_bij m r hm5 hr5 hrm hodd hmodd hm hcop) M B hB1
    (branch_lift S0 M Mbar hM B hB) (fun u => S0.π u ≠ 0)
  · intro u hu h0; apply hu; rw [h0, map_zero]
  · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Fintype.card_pos.le)
  · intro u v hu
    unfold DP
    apply div_le_div_of_nonneg_right _ (by exact_mod_cast Fintype.card_pos.le)
    rw [dd_eq_delta]
    exact_mod_cast (S0.fam5_units' hcard m r hm5 hr5 hrm hodd hmodd hm hcop u v hu).1
  · -- residue branch: unit words of `x` are those of `a`, and the residue of `M x` is `M̄ x̄`
    intro x hx
    have h1 := left_ne_zero_of_mul hx
    rw [Finset.prod_ne_zero_iff] at h1
    have hunit : ∀ j, S0.π (x j) ≠ 0 ↔ S0.π (a j) ≠ 0 := by
      intro j
      have hj := h1 j (mem_univ _)
      unfold DP at hj
      have hdd : dd (fun y : R => (APN2.Fsh5 R m r).eval y) (a j) (x j) ≠ 0 := by
        intro h; apply hj; rw [h]; simp
      obtain ⟨⟨y, hy⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hdd)
      have hy' : (APN2.Fsh5 R m r).eval (y + a j) - (APN2.Fsh5 R m r).eval y = x j := hy
      rw [← hy']
      constructor
      · intro h1 h2
        apply h1
        rw [map_sub, S0.pi_eval, S0.pi_eval, map_add, h2, add_zero, sub_self]
      · intro h1
        exact S0.unit_diff (APN2.Fsh5 R m r) hinj y (a j) h1
    set xb : Fin n → K := fun i => S0.π (x i)
    have hxb : xb ≠ 0 := by
      obtain ⟨j, hj⟩ := ha
      intro h
      exact (hunit j).mpr hj (congrFun h j)
    have hb := hB xb hxb
    convert hb using 2
    · unfold wt; apply congrArg Finset.card; ext j
      simp only [mem_filter, mem_univ, true_and, xb]; exact (hunit j).symm
    · unfold wt; apply congrArg Finset.card; ext j
      simp only [mem_filter, mem_univ, true_and, xb, ← hM]

/-- the fixed-key form -/
theorem fam5_fixed_key_unit (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (a b : Fin n → R) (ha : ∃ j, S0.π (a j) ≠ 0) (t : ℚ) (ht : 0 < t) :
    ((univ.filter (fun κ : (Fin n → R) × (Fin n → R) =>
        t ≤ ((univ.filter (fun x0 : Fin n → R =>
          out2 (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M a x0 κ.1 κ.2 = b)).card : ℚ) /
            Fintype.card (Fin n → R))).card : ℚ) / Fintype.card ((Fin n → R) × (Fin n → R)) ≤
      2 ^ n * (((2 * Fintype.card K : ℕ) : ℚ) / Fintype.card R) ^ (B - 1) / t :=
  fixed_key_markov _ M a b t ht _
    (fam5_diff2_unit S0 hcard m r hm5 hr5 hrm hodd hmodd hm hcop M Mbar hM B hB1 hB a b ha)

end APN2.Markov

#print axioms APN2.Markov.hull_core
#print axioms APN2.Markov.hull2_unit
#print axioms APN2.Markov.fam5_diff2_unit
#print axioms APN2.Markov.fam5_fixed_key_unit
