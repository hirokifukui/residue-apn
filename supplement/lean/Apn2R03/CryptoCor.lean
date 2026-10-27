import Apn2R03.Markov
import Apn2R03.ResAPN

/-!
# Transition probabilities of characteristics (Claude, 2026-10-25; paper Cor. "Transition probabilities", 2nd half)

`N` rounds `x ↦ M (S x) + κ` on `G = (Fin n → R)`, `S` applying `F : R[X]` to each word, `M : G ≃+ G`.
If every unit-direction row of the difference table of `F` is bounded by `D`, the residue map of `F`
is injective, `M` reduces mod `π` to `Mbar` with branch number `B`, and `Δ 0` has a unit coordinate,
then any characteristic `Δ` has probability `≤ (D/|R|)^(B ⌊N/2⌋)`.
-/

set_option linter.unusedSectionVars false

namespace APN2.Markov

open Finset Polynomial

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- number of nonzero coordinates -/
def wt {n : ℕ} (u : Fin n → K) : ℕ := (univ.filter (fun j => u j ≠ 0)).card

/-- coordinatewise residue -/
def rd (S0 : APN2.GRS R K) {n : ℕ} (v : Fin n → R) : Fin n → K := fun j => S0.π (v j)

/-- bridge: the two difference-table counts agree -/
theorem dd_eq_delta (F : R[X]) (a b : R) : dd (fun x => F.eval x) a b = APN2.GRS.delta F a b := by
  unfold dd APN2.GRS.delta
  rw [Fintype.card_subtype]

/-- branch-number counting with the pair hypothesis only inside the window -/
theorem sum_active_ge' (a : ℕ → ℕ) (B : ℕ) : ∀ N, (∀ i, i + 1 < N → B ≤ a i + a (i + 1)) →
    B * (N / 2) ≤ ∑ i ∈ range N, a i := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro h
    match N with
    | 0 => simp
    | 1 => simp
    | N + 2 =>
      have h1 := ih N (by omega) (fun i hi => h i (by omega))
      rw [sum_range_succ, sum_range_succ]
      have h2 : (N + 2) / 2 = N / 2 + 1 := by omega
      rw [h2, Nat.mul_succ]
      have := h N (by omega)
      omega

/-- one round: a possible transition preserves the unit pattern coordinatewise -/
theorem round_pattern (S0 : APN2.GRS R K) {n : ℕ} (F : R[X])
    (hinj : Function.Injective (fun t : K => (F.map S0.π).eval t)) (α β : Fin n → R)
    (h : dd (fun x : Fin n → R => fun j => F.eval (x j)) α β ≠ 0) (j : Fin n) :
    S0.π (β j) ≠ 0 ↔ S0.π (α j) ≠ 0 := by
  obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h)
  have hj : F.eval (x j + α j) - F.eval (x j) = β j := by
    have := congrFun hx j
    simpa using this
  rw [← hj]
  constructor
  · intro h1 h2
    apply h1
    rw [map_sub, S0.pi_eval, S0.pi_eval, map_add, h2, add_zero, sub_self]
  · intro h1
    exact S0.unit_diff F hinj (x j) (α j) h1

/-- the reduction of `M` has trivial kernel -/
theorem res_ker (S0 : APN2.GRS R K) {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R))
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j) :
    ∀ v, rd S0 (M v) = 0 → rd S0 v = 0 := by
  have hT : ∀ w, rd S0 w = 0 → rd S0 (M w) = 0 := by
    intro w hw
    funext j
    show S0.π (M w j) = 0
    rw [hM w j]
    have : (fun i => S0.π (w i)) = fun i => S0.π ((0 : Fin n → R) i) := by
      funext i
      have := congrFun hw i
      simp only [rd, Pi.zero_apply] at this
      simp [this]
    rw [this, ← hM 0 j]
    simp
  intro v hv
  let T := univ.filter (fun w : Fin n → R => rd S0 w = 0)
  have himg : T.image M = T := by
    apply eq_of_subset_of_card_le
    · intro y hy
      simp only [mem_image, T, mem_filter, mem_univ, true_and] at hy ⊢
      obtain ⟨w, hw, rfl⟩ := hy
      exact hT w hw
    · rw [card_image_of_injective _ M.injective]
  have hmem : M v ∈ T.image M := by
    rw [himg]
    simp [T, hv]
  obtain ⟨w, hw, hwv⟩ := mem_image.mp hmem
  rw [← M.injective hwv]
  simpa [T] using hw

/-- one round factor: `dd/|G| ≤ (D/|R|)^(number of unit input coordinates)` -/
theorem factor_le (S0 : APN2.GRS R K) {n : ℕ} (F : R[X]) (D : ℕ)
    (hunit : ∀ a b : R, S0.π a ≠ 0 → APN2.GRS.delta F a b ≤ D)
    (α β : Fin n → R) :
    (dd (fun x : Fin n → R => fun j => F.eval (x j)) α β : ℚ) / Fintype.card (Fin n → R) ≤
      ((D : ℚ) / Fintype.card R) ^ wt (rd S0 α) := by
  have hR : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hpi : dd (fun x : Fin n → R => fun j => F.eval (x j)) α β =
      ∏ j, dd (fun y : R => F.eval y) (α j) (β j) := dd_pi (fun y : R => F.eval y) α β
  have hc : ((Fintype.card R : ℚ) ^ n) = ∏ _j : Fin n, (Fintype.card R : ℚ) := by simp
  rw [hpi, Nat.cast_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, hc, ← prod_div_distrib]
  calc ∏ j, ((dd (fun y : R => F.eval y) (α j) (β j) : ℚ) / Fintype.card R)
      ≤ ∏ j : Fin n, (if S0.π (α j) ≠ 0 then (D : ℚ) / Fintype.card R else 1) := by
        apply prod_le_prod
        · intro j _; positivity
        · intro j _
          split_ifs with hj
          · gcongr
            have := hunit (α j) (β j) hj
            rw [← dd_eq_delta] at this
            exact_mod_cast this
          · rw [div_le_one hR]
            have : dd (fun y : R => F.eval y) (α j) (β j) ≤ Fintype.card R :=
              Fintype.card_subtype_le _
            exact_mod_cast this
    _ = ((D : ℚ) / Fintype.card R) ^ wt (rd S0 α) := by
        rw [prod_ite, prod_const, prod_const_one, mul_one]
        rfl

open scoped Classical in
/-- **Corollary (transition probabilities, second half).** -/
theorem char_prob_le (S0 : APN2.GRS R K) {n : ℕ} (F : R[X]) (M : (Fin n → R) ≃+ (Fin n → R))
    (Δ : ℕ → (Fin n → R)) (N D B : ℕ)
    (hunit : ∀ a b : R, S0.π a ≠ 0 → APN2.GRS.delta F a b ≤ D)
    (hD : D ≤ Fintype.card R)
    (hinj : Function.Injective (fun t : K => (F.map S0.π).eval t))
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hΔ : ∃ j, S0.π (Δ 0 j) ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => F.eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤ ((D : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  have hR : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hp0 : (0 : ℚ) ≤ (D : ℚ) / Fintype.card R := div_nonneg (Nat.cast_nonneg _) hR.le
  have hp1 : (D : ℚ) / Fintype.card R ≤ 1 := (div_le_one hR).mpr (by exact_mod_cast hD)
  rw [trail_prob]
  by_cases hz : ∃ i ∈ range N,
      dd (fun x : Fin n → R => fun j => F.eval (x j)) (Δ i) (M.symm (Δ (i + 1))) = 0
  · obtain ⟨i, hi, h0⟩ := hz
    rw [prod_eq_zero hi (by rw [h0]; simp)]
    exact pow_nonneg hp0 _
  push Not at hz
  have hker := res_ker S0 M Mbar hM
  have hround : ∀ i < N, ∀ j, S0.π (M.symm (Δ (i + 1)) j) ≠ 0 ↔ S0.π (Δ i j) ≠ 0 :=
    fun i hi j => round_pattern S0 F hinj _ _ (hz i (mem_range.mpr hi)) j
  have hwt : ∀ i < N, wt (rd S0 (M.symm (Δ (i + 1)))) = wt (rd S0 (Δ i)) := by
    intro i hi
    unfold wt rd
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact hround i hi j
  have hMbar : ∀ i, Mbar (rd S0 (M.symm (Δ (i + 1)))) = rd S0 (Δ (i + 1)) := by
    intro i
    funext j
    unfold rd
    rw [← hM]
    simp
  have hu : ∀ i < N, rd S0 (Δ i) ≠ 0 → rd S0 (M.symm (Δ (i + 1))) ≠ 0 := by
    intro i hi h1 h3
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h1
    exact ((hround i hi j).mpr hj) (congrFun h3 j)
  have hnz : ∀ i, i ≤ N → rd S0 (Δ i) ≠ 0 := by
    intro i
    induction i with
    | zero =>
      intro _ h
      obtain ⟨j, hj⟩ := hΔ
      exact hj (congrFun h j)
    | succ i ih =>
      intro hi h
      apply hu i (by omega) (ih (by omega))
      apply hker
      simpa using h
  have hpair : ∀ i < N, B ≤ wt (rd S0 (Δ i)) + wt (rd S0 (Δ (i + 1))) := by
    intro i hi
    have := hB _ (hu i hi (hnz i (by omega)))
    rwa [hwt i hi, hMbar i] at this
  have hk := sum_active_ge' (fun i => wt (rd S0 (Δ i))) B N (fun i hi => hpair i (by omega))
  exact prod_le_pow_of_active N B
    (fun i => (dd (fun x : Fin n → R => fun j => F.eval (x j)) (Δ i) (M.symm (Δ (i + 1))) : ℚ) /
      Fintype.card (Fin n → R)) _ hp0 hp1 _ hk
    (fun i _ => ⟨by positivity, factor_le S0 F D hunit _ _⟩)

open scoped Classical in
/-- instantiation for the r = 3 lift `F♯ = Fsh3 R m` with `D = 2q` -/
theorem char_prob_le_fam3 (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m : ℕ) (hm5 : 5 ≤ m) (hodd : Odd m) (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Δ : ℕ → (Fin n → R)) (N B : ℕ)
    (hinj : Function.Injective (fun t : K => ((APN2.Fsh3 R m).map S0.π).eval t))
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hΔ : ∃ j, S0.π (Δ 0 j) ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => (APN2.Fsh3 R m).eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤
      (((2 * Fintype.card K : ℕ) : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  apply char_prob_le S0 _ M Δ N _ B _ _ hinj Mbar hM hB hΔ
  · intro a b ha
    exact (S0.fam3_units' hcard m hm5 hodd hm h3 a b ha).1
  · rw [hcard]
    have hq : 2 ≤ Fintype.card K := by
      rw [hm]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hk := S0.hk
    calc 2 * Fintype.card K ≤ Fintype.card K * Fintype.card K := Nat.mul_le_mul_right _ hq
      _ = Fintype.card K ^ 2 := (sq _).symm
      _ ≤ Fintype.card K ^ S0.k := Nat.pow_le_pow_right (by omega) (by omega)

open scoped Classical in
/-- instantiation for the r ≥ 5 lift `F♯ = Fsh5 R m r` with `D = 2q` -/
theorem char_prob_le_fam5 (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Δ : ℕ → (Fin n → R)) (N B : ℕ)
    (hinj : Function.Injective (fun t : K => ((APN2.Fsh5 R m r).map S0.π).eval t))
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hΔ : ∃ j, S0.π (Δ 0 j) ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤
      (((2 * Fintype.card K : ℕ) : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  apply char_prob_le S0 _ M Δ N _ B _ _ hinj Mbar hM hB hΔ
  · intro a b ha
    exact (S0.fam5_units' hcard m r hm5 hr5 hrm hodd hmodd hm hcop a b ha).1
  · rw [hcard]
    have hq : 2 ≤ Fintype.card K := by
      rw [hm]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hk := S0.hk
    calc 2 * Fintype.card K ≤ Fintype.card K * Fintype.card K := Nat.mul_le_mul_right _ hq
      _ = Fintype.card K ^ 2 := (sq _).symm
      _ ≤ Fintype.card K ^ S0.k := Nat.pow_le_pow_right (by omega) (by omega)

end APN2.Markov
