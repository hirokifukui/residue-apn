import Apn2R03.HullUnit
import Apn2R03.Layered

/-!
# Layerwise two-round differentials without the factor `2^n` (Claude, 2026-10-26, R06)

GPT R05c review §4. When the output difference `b` is fixed, the second S-box layer has the fixed target
`c = M⁻¹ b`; valuation preservation then fixes the exact-layer support of `M x` to that of `c`, so no
splitting by a variable pattern is needed.

* `hull2_digit`  : abstract form: an invariant word class `V`, a digit map `φ`, the digit pattern is kept by the
                   S-box and mapped by `M̄`; rows with input in `V` and nonzero digit bounded by `p` ⇒ the two-round
                   sum is `≤ p^(B−1)`;
* `diff2_layer`  : over `R_k`, any S-box `F` that permutes `R_k`, with residue permutation and `p'` zero-free:
                   an input difference whose words lie in `2^s R` with one word of exact valuation `s` has every
                   two-round differential of probability `≤ (D_s/q^k)^(B−1)`, where `D_s` bounds the rows
                   `δ_F(2^s y, ·)`, `y` a unit;
* `fixed_key_layer` : the fixed-key (Markov) form;
* `fam5_diff2_unit_sharp` : `F♯` (`r ≥ 5`), unit layer: `≤ (2q/q^k)^(B−1)` (replaces `2^n (2q/q^k)^(B−1)`);
* `fam5_diff2_mid` : `F♯` (`r ≥ 5`), layer `1 ≤ s ≤ k−2`: `≤ (q^(s+1)/q^k)^(B−1)`;
* `diff2_top`    : the top layer, any lift with `p'` zero-free and two-to-one: `≤ (2q^(k−1)/q^k)^(B−1)`.
-/

set_option linter.unusedSectionVars false

namespace APN2.Markov

open Finset Polynomial APN2R03

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

open scoped Classical in
/-- **Two-round differentials through a fixed digit pattern** (abstract form). -/
theorem hull2_digit {n : ℕ} (s : R → R) (hs : Function.Bijective s)
    (M : (Fin n → R) ≃+ (Fin n → R)) (B : ℕ) (hB1 : 1 ≤ B)
    (hBG : ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x))
    (V : R → Prop) (φ : R → K) (Mbar : (Fin n → K) → (Fin n → K))
    (hφ0 : φ 0 = 0)
    (hVS : ∀ u v : R, V u → DP s u v ≠ 0 → V v)
    (hVM : ∀ w : Fin n → R, (∀ j, V (w j)) → ∀ j, V (M w j))
    (hφS : ∀ u v : R, V u → DP s u v ≠ 0 → (φ v ≠ 0 ↔ φ u ≠ 0))
    (hφM : ∀ w : Fin n → R, (∀ j, V (w j)) → ∀ j, φ (M w j) = Mbar (fun i => φ (w i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (p : ℚ) (hp0 : 0 ≤ p) (hp : ∀ u v : R, V u → φ u ≠ 0 → DP s u v ≤ p)
    (a c : Fin n → R) (haV : ∀ j, V (a j)) (ha : ∃ j, φ (a j) ≠ 0) :
    ∑ x : Fin n → R, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≤ p ^ (B - 1) := by
  by_cases hex : ∃ x : Fin n → R, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0
  swap
  · push Not at hex
    rw [Finset.sum_eq_zero (fun x _ => hex x)]
    exact pow_nonneg hp0 _
  have hfacts : ∀ x : Fin n → R, (∏ j, DP s (a j) (x j)) * (∏ j, DP s (M x j) (c j)) ≠ 0 →
      (∀ j, V (x j)) ∧ (∀ j, V (M x j)) ∧
      (∀ j, φ (x j) ≠ 0 ↔ φ (a j) ≠ 0) ∧ (∀ j, φ (c j) ≠ 0 ↔ φ (M x j) ≠ 0) := by
    intro x hx
    have h1 := left_ne_zero_of_mul hx
    have h2 := right_ne_zero_of_mul hx
    rw [Finset.prod_ne_zero_iff] at h1 h2
    have hxV : ∀ j, V (x j) := fun j => hVS _ _ (haV j) (h1 j (mem_univ _))
    have hMV : ∀ j, V (M x j) := hVM x hxV
    exact ⟨hxV, hMV, fun j => hφS _ _ (haV j) (h1 j (mem_univ _)),
      fun j => hφS _ _ (hMV j) (h2 j (mem_univ _))⟩
  obtain ⟨x0, hx0⟩ := hex
  obtain ⟨hxV, _, hxa, hcM⟩ := hfacts x0 hx0
  have hcnt : B ≤ (univ.filter (fun j => φ (a j) ≠ 0)).card +
      (univ.filter (fun j => φ (c j) ≠ 0)).card := by
    have hu0 : (fun i => φ (x0 i)) ≠ 0 := by
      intro h
      obtain ⟨j, hj⟩ := ha
      exact (hxa j).mpr hj (congrFun h j)
    have hb := hB _ hu0
    have e1 : wt (fun i => φ (x0 i)) = (univ.filter (fun j => φ (a j) ≠ 0)).card := by
      unfold wt; apply congrArg Finset.card; ext j
      simp only [mem_filter, mem_univ, true_and]; exact hxa j
    have e2 : wt (Mbar (fun i => φ (x0 i))) = (univ.filter (fun j => φ (c j) ≠ 0)).card := by
      unfold wt; apply congrArg Finset.card; ext j
      simp only [mem_filter, mem_univ, true_and]
      rw [← hφM x0 hxV j]; exact (hcM j).symm
    omega
  obtain ⟨A', hA'U, hA'c⟩ := Finset.exists_subset_card_eq
    (s := univ.filter (fun j => φ (a j) ≠ 0))
    (n := min (univ.filter (fun j => φ (a j) ≠ 0)).card (B - 1)) (min_le_left _ _)
  obtain ⟨C', hC'U, hC'c⟩ := Finset.exists_subset_card_eq
    (s := univ.filter (fun j => φ (c j) ≠ 0)) (n := B - 1 - A'.card) (by omega)
  have hφne : ∀ w : R, φ w ≠ 0 → w ≠ 0 := fun w hw h => hw (by rw [h, hφ0])
  apply hull_core s hs M B hB1 hBG p hp0 a c univ A' C'
    (fun j hj => hφne _ (Finset.mem_filter.mp (hA'U hj)).2)
    (fun j hj => hφne _ (Finset.mem_filter.mp (hC'U hj)).2) (by omega)
  · intro x _ _ j hj
    exact hp _ _ (haV j) (Finset.mem_filter.mp (hA'U hj)).2
  · intro x _ hx j hj
    obtain ⟨_, hMV', _, hcM'⟩ := hfacts x hx
    exact hp _ _ (hMV' j) ((hcM' j).mp (Finset.mem_filter.mp (hC'U hj)).2)

open scoped Classical in
/-- the probability form of `hull2_digit` -/
theorem diff2_digit {n : ℕ} (s : R → R) (hs : Function.Bijective s)
    (M : (Fin n → R) ≃+ (Fin n → R)) (B : ℕ) (hB1 : 1 ≤ B)
    (hBG : ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x))
    (V : R → Prop) (φ : R → K) (Mbar : (Fin n → K) → (Fin n → K))
    (hφ0 : φ 0 = 0)
    (hVS : ∀ u v : R, V u → DP s u v ≠ 0 → V v)
    (hVM : ∀ w : Fin n → R, (∀ j, V (w j)) → ∀ j, V (M w j))
    (hφS : ∀ u v : R, V u → DP s u v ≠ 0 → (φ v ≠ 0 ↔ φ u ≠ 0))
    (hφM : ∀ w : Fin n → R, (∀ j, V (w j)) → ∀ j, φ (M w j) = Mbar (fun i => φ (w i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (p : ℚ) (hp0 : 0 ≤ p) (hp : ∀ u v : R, V u → φ u ≠ 0 → DP s u v ≤ p)
    (a b : Fin n → R) (haV : ∀ j, V (a j)) (ha : ∃ j, φ (a j) ≠ 0) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => s (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤ p ^ (B - 1) := by
  rw [prob_out2]
  simp only [dd_word]
  exact hull2_digit s hs M B hB1 hBG V φ Mbar hφ0 hVS hVM hφS hφM hB p hp0 hp a (M.symm b) haV ha

open scoped Classical in
/-- **Two-round differentials in layer `s`** over `R_k`, for any S-box `F` that permutes `R_k`, reduces to a
permutation and has `p'` zero-free. -/
theorem diff2_layer (S0 : APN2.GRS R K) (F : R[X])
    (hbij : Function.Bijective (fun x : R => F.eval x))
    (hinj : Function.Injective (fun t : K => (F.map S0.π).eval t))
    (hp' : ∀ t, (F.map S0.π).derivative.eval t ≠ 0)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (s D : ℕ) (hsk : s < S0.k)
    (hD : ∀ y b : R, S0.π y ≠ 0 → APN2.GRS.delta F (2 ^ s * y) b ≤ D)
    (a b : Fin n → R) (haV : ∀ j, ∃ y, a j = 2 ^ s * y)
    (ha : ∃ j y, a j = 2 ^ s * y ∧ S0.π y ≠ 0) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => F.eval (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤
      ((D : ℚ) / Fintype.card R) ^ (B - 1) := by
  have hstep : ∀ u v : R, DP (fun y : R => F.eval y) u v ≠ 0 →
      ∃ x, F.eval (x + u) - F.eval x = v := by
    intro u v h
    have hdd : dd (fun y : R => F.eval y) u v ≠ 0 := by
      intro h0; apply h; unfold DP; rw [h0]; simp
    obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hdd)
    exact ⟨x, hx⟩
  refine diff2_digit (fun y : R => F.eval y) hbij M B hB1 (branch_lift S0 M Mbar hM B hB)
    (fun w => ∃ y, w = 2 ^ s * y) (S0.digit s) Mbar ?_ ?_ ?_ ?_ ?_ hB _ ?_ ?_ a b haV ?_
  · have := S0.digit_eq s hsk 0
    rw [mul_zero, map_zero] at this
    exact this
  · -- the S-box keeps the layer
    rintro u v ⟨y, rfl⟩ h
    obtain ⟨x, rfl⟩ := hstep _ _ h
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub (x + 2 ^ s * y) x F
    rw [add_sub_cancel_left] at hc
    exact ⟨y * c, by rw [hc]; ring⟩
  · -- `M` keeps the layer
    intro v hv j
    choose Y hY using hv
    have hvY : v = (2 ^ s : ℕ) • Y := by funext i; simp [hY i, nsmul_eq_mul]
    refine ⟨M Y j, ?_⟩
    rw [hvY, map_nsmul]
    simp [nsmul_eq_mul]
  · -- valuation preservation
    rintro u v ⟨y, rfl⟩ h
    obtain ⟨x, rfl⟩ := hstep _ _ h
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · have e0 : ∀ w : R, S0.digit 0 w = S0.π w := fun w => by
        simpa using S0.digit_eq 0 hsk w
      rw [e0, e0]
      simp only [pow_zero, one_mul]
      constructor
      · intro h1 h2
        apply h1
        rw [map_sub, S0.pi_eval, S0.pi_eval, map_add, h2, add_zero, sub_self]
      · intro h1
        exact S0.unit_diff F hinj x y h1
    · obtain ⟨Q, hQ⟩ := taylor2 F x (2 ^ s * y)
      have e : F.eval (x + 2 ^ s * y) - F.eval x =
          2 ^ s * (y * F.derivative.eval x + 2 ^ s * (y ^ 2 * Q)) := by rw [hQ]; ring
      rw [e, S0.digit_eq s hsk, S0.digit_eq s hsk, map_add, map_mul, S0.pi_two_pow_mul s hs1,
        add_zero, S0.pi_deriv_eval]
      constructor
      · intro h1 h2; apply h1; rw [h2, zero_mul]
      · intro h1; exact mul_ne_zero h1 (hp' _)
  · -- `M` on digits
    intro v hv j
    choose Y hY using hv
    have hvY : v = (2 ^ s : ℕ) • Y := by funext i; simp [hY i, nsmul_eq_mul]
    have hMv : M v j = 2 ^ s * M Y j := by rw [hvY, map_nsmul]; simp [nsmul_eq_mul]
    rw [hMv, S0.digit_eq s hsk, hM]
    congr 1
    funext i
    rw [hY i, S0.digit_eq s hsk]
  · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Fintype.card_pos.le)
  · rintro u v ⟨y, rfl⟩ hy
    rw [S0.digit_eq s hsk] at hy
    unfold DP
    apply div_le_div_of_nonneg_right _ (by exact_mod_cast Fintype.card_pos.le)
    rw [dd_eq_delta]
    exact_mod_cast hD y v hy
  · obtain ⟨j, y, hj, hy⟩ := ha
    exact ⟨j, by rw [hj, S0.digit_eq s hsk]; exact hy⟩

open scoped Classical in
/-- the fixed-key form of `diff2_layer` -/
theorem fixed_key_layer (S0 : APN2.GRS R K) (F : R[X])
    (hbij : Function.Bijective (fun x : R => F.eval x))
    (hinj : Function.Injective (fun t : K => (F.map S0.π).eval t))
    (hp' : ∀ t, (F.map S0.π).derivative.eval t ≠ 0)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (s D : ℕ) (hsk : s < S0.k)
    (hD : ∀ y b : R, S0.π y ≠ 0 → APN2.GRS.delta F (2 ^ s * y) b ≤ D)
    (a b : Fin n → R) (haV : ∀ j, ∃ y, a j = 2 ^ s * y)
    (ha : ∃ j y, a j = 2 ^ s * y ∧ S0.π y ≠ 0) (t : ℚ) (ht : 0 < t) :
    ((univ.filter (fun κ : (Fin n → R) × (Fin n → R) =>
        t ≤ ((univ.filter (fun x0 : Fin n → R =>
          out2 (fun x : Fin n → R => fun j => F.eval (x j)) M a x0 κ.1 κ.2 = b)).card : ℚ) /
            Fintype.card (Fin n → R))).card : ℚ) / Fintype.card ((Fin n → R) × (Fin n → R)) ≤
      ((D : ℚ) / Fintype.card R) ^ (B - 1) / t :=
  fixed_key_markov _ M a b t ht _
    (diff2_layer S0 F hbij hinj hp' M Mbar hM B hB1 hB s D hsk hD a b haV ha)

open scoped Classical in
/-- **`F♯` (`r ≥ 5`), unit layer**: every two-round differential whose input has a unit word has probability
`≤ (2q/q^k)^(B−1)` (no factor `2^n`). -/
theorem fam5_diff2_unit_sharp (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (a b : Fin n → R) (ha : ∃ j, S0.π (a j) ≠ 0) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤
      (((2 * Fintype.card K : ℕ) : ℚ) / Fintype.card R) ^ (B - 1) := by
  haveI := S0.charP2
  have hk := S0.hk
  apply diff2_layer S0 _ (S0.fam5_bij m r hm5 hr5 hrm hodd hmodd hm hcop)
    (by rw [S0.fam5_sh_map]; exact resPerm5 m r hm5 hr5 hmodd hm hcop hodd)
    (by rw [S0.fam5_sh_map]; exact p5_deriv_ne m r hm5 hr5 hmodd hm) M Mbar hM B hB1 hB 0 _ (by omega)
  · intro y v hy
    rw [pow_zero, one_mul]
    exact (S0.fam5_units' hcard m r hm5 hr5 hrm hodd hmodd hm hcop y v hy).1
  · intro j; exact ⟨a j, by ring⟩
  · obtain ⟨j, hj⟩ := ha
    exact ⟨j, a j, by ring, hj⟩

open scoped Classical in
/-- **`F♯` (`r ≥ 5`), layer `1 ≤ s ≤ k−2`**: `≤ (q^(s+1)/q^k)^(B−1)`. -/
theorem fam5_diff2_mid (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (s : ℕ) (hs1 : 1 ≤ s) (hsk : s + 2 ≤ S0.k)
    (a b : Fin n → R) (haV : ∀ j, ∃ y, a j = 2 ^ s * y) (ha : ∃ j y, a j = 2 ^ s * y ∧ S0.π y ≠ 0) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤
      (((Fintype.card K ^ (s + 1) : ℕ) : ℚ) / Fintype.card R) ^ (B - 1) := by
  haveI := S0.charP2
  apply diff2_layer S0 _ (S0.fam5_bij m r hm5 hr5 hrm hodd hmodd hm hcop)
    (by rw [S0.fam5_sh_map]; exact resPerm5 m r hm5 hr5 hmodd hm hcop hodd)
    (by rw [S0.fam5_sh_map]; exact p5_deriv_ne m r hm5 hr5 hmodd hm) M Mbar hM B hB1 hB s _ (by omega)
  · intro y v hy
    rcases S0.fam5_interfamily hcard m r hm5 hr5 hrm hodd hmodd hm hcop s hs1 hsk y v hy with h | h
    · rw [h]; exact Nat.zero_le _
    · exact h.le
  · exact haV
  · exact ha

open scoped Classical in
/-- **Top layer** (any S-box `F` as in `diff2_layer` whose `p'` is two-to-one): `≤ (2q^(k−1)/q^k)^(B−1)`. -/
theorem diff2_top (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k) (F : R[X]) (ρ : K)
    (hbij : Function.Bijective (fun x : R => F.eval x))
    (hinj : Function.Injective (fun t : K => (F.map S0.π).eval t))
    (hp' : ∀ t, (F.map S0.π).derivative.eval t ≠ 0)
    (hd2 : ∀ a b : K, (F.map S0.π).derivative.eval a = (F.map S0.π).derivative.eval b → b = a ∨ b = a + ρ)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (a b : Fin n → R) (haV : ∀ j, ∃ y, a j = 2 ^ (S0.k - 1) * y)
    (ha : ∃ j y, a j = 2 ^ (S0.k - 1) * y ∧ S0.π y ≠ 0) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => F.eval (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤
      (((2 * Fintype.card K ^ (S0.k - 1) : ℕ) : ℚ) / Fintype.card R) ^ (B - 1) := by
  have hk := S0.hk
  exact diff2_layer S0 F hbij hinj hp' M Mbar hM B hB1 hB (S0.k - 1) _ (by omega)
    (fun y v hy => S0.top_layer_le hcard F ρ hd2 y v hy) a b haV ha

end APN2.Markov

#print axioms APN2.Markov.hull2_digit
#print axioms APN2.Markov.diff2_digit
#print axioms APN2.Markov.diff2_layer
#print axioms APN2.Markov.fixed_key_layer
#print axioms APN2.Markov.fam5_diff2_unit_sharp
#print axioms APN2.Markov.fam5_diff2_mid
#print axioms APN2.Markov.diff2_top
