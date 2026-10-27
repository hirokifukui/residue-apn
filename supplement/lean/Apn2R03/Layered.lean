import Apn2R03.CryptoCor
import Apn2R03.InterFam

/-!
# Characteristics in the lower layers (Claude, 2026-10-26, R05c)

The branch-number argument of `char_prob_le` works in every 2-adic layer. A characteristic whose input
difference has all words in `2^s R` and some word in `2^s R \ 2^(s+1) R` stays in this layer, the pattern of
words of exact valuation `s` is preserved by the S-box layer (valuation preservation) and mapped by `M̄`, so
* `char_prob_le_digit` : the abstract statement for any "digit" map `φ` and any invariant word set `V`;
* `char_prob_le_layer` : layer `s ≥ 1` of `R_k`, if `p'` has no zero and the rows of the layer are bounded by `D_s`;
* `top_layer_le`       : the top layer `2^(k−1) R` has entries `≤ 2 q^(k−1)` (for every lift);
* `char_prob_le_fam5_layer` : for `F♯` (`r ≥ 5`): probability `≤ (q^(s+1)/q^k)^(B ⌊N/2⌋)` in layer
  `1 ≤ s ≤ k−2` and `≤ (2 q^(k−1)/q^k)^(B ⌊N/2⌋)` in the top layer.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

/-- the digit of `w ∈ 2^s R`: the residue of `w / 2^s` -/
noncomputable def digit (s : ℕ) (w : R) : K :=
  by classical exact if h : ∃ y, w = 2 ^ s * y then S.π h.choose else 0

theorem digit_eq (s : ℕ) (hs : s < S.k) (y : R) : S.digit s (2 ^ s * y) = S.π y := by
  classical
  have h : ∃ y', 2 ^ s * y = 2 ^ s * y' := ⟨y, rfl⟩
  unfold digit
  rw [dif_pos h]
  have e : (2 : R) ^ s * (h.choose - y) = 0 := by rw [mul_sub, ← h.choose_spec, sub_self]
  obtain ⟨z, hz⟩ := S.ann_two_pow s (S.k - s) (by omega) _ e
  have : S.π (h.choose - y) = 0 := by rw [hz]; exact S.pi_two_pow_mul _ (by omega) _
  rwa [map_sub, sub_eq_zero] at this

end GRS

namespace Markov

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

open scoped Classical in
/-- one round factor with an arbitrary "active" predicate -/
theorem factor_le_gen {n : ℕ} (F : R[X]) (D : ℕ) (P : R → Prop)
    (hP : ∀ a b : R, P a → APN2.GRS.delta F a b ≤ D) (α β : Fin n → R) :
    (dd (fun x : Fin n → R => fun j => F.eval (x j)) α β : ℚ) / Fintype.card (Fin n → R) ≤
      ((D : ℚ) / Fintype.card R) ^ (univ.filter (fun j => P (α j))).card := by
  have hR : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hpi : dd (fun x : Fin n → R => fun j => F.eval (x j)) α β =
      ∏ j, dd (fun y : R => F.eval y) (α j) (β j) := dd_pi (fun y : R => F.eval y) α β
  have hc : ((Fintype.card R : ℚ) ^ n) = ∏ _j : Fin n, (Fintype.card R : ℚ) := by simp
  rw [hpi, Nat.cast_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, hc, ← prod_div_distrib]
  calc ∏ j, ((dd (fun y : R => F.eval y) (α j) (β j) : ℚ) / Fintype.card R)
      ≤ ∏ j : Fin n, (if P (α j) then (D : ℚ) / Fintype.card R else 1) := by
        apply prod_le_prod
        · intro j _; positivity
        · intro j _
          split_ifs with hj
          · gcongr
            have := hP (α j) (β j) hj
            rw [← dd_eq_delta] at this
            exact_mod_cast this
          · rw [div_le_one hR]
            have : dd (fun y : R => F.eval y) (α j) (β j) ≤ Fintype.card R :=
              Fintype.card_subtype_le _
            exact_mod_cast this
    _ = ((D : ℚ) / Fintype.card R) ^ (univ.filter (fun j => P (α j))).card := by
        rw [prod_ite, prod_const, prod_const_one, mul_one]

open scoped Classical in
/-- **Characteristics through an invariant layer** (abstract form). -/
theorem char_prob_le_digit {n : ℕ} (F : R[X]) (M : (Fin n → R) ≃+ (Fin n → R))
    (Δ : ℕ → (Fin n → R)) (N D B : ℕ) (V : R → Prop) (φ : R → K)
    (Mbar : (Fin n → K) → (Fin n → K))
    (hVS : ∀ a b : R, V a → dd (fun y : R => F.eval y) a b ≠ 0 → V b)
    (hVM : ∀ v : Fin n → R, (∀ j, V (v j)) → ∀ j, V (M v j))
    (hφS : ∀ a b : R, V a → dd (fun y : R => F.eval y) a b ≠ 0 → (φ b ≠ 0 ↔ φ a ≠ 0))
    (hφM : ∀ v : Fin n → R, (∀ j, V (v j)) → ∀ j, φ (M v j) = Mbar (fun i => φ (v i)) j)
    (hMinj : ∀ u, Mbar u = 0 → u = 0)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hD : ∀ a b : R, V a → φ a ≠ 0 → APN2.GRS.delta F a b ≤ D) (hDR : D ≤ Fintype.card R)
    (hΔV : ∀ j, V (Δ 0 j)) (hΔ : ∃ j, φ (Δ 0 j) ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => F.eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤ ((D : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  have hR : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hp0 : (0 : ℚ) ≤ (D : ℚ) / Fintype.card R := div_nonneg (Nat.cast_nonneg _) hR.le
  have hp1 : (D : ℚ) / Fintype.card R ≤ 1 := (div_le_one hR).mpr (by exact_mod_cast hDR)
  rw [trail_prob]
  by_cases hz : ∃ i ∈ range N,
      dd (fun x : Fin n → R => fun j => F.eval (x j)) (Δ i) (M.symm (Δ (i + 1))) = 0
  · obtain ⟨i, hi, h0⟩ := hz
    rw [prod_eq_zero hi (by rw [h0]; simp)]
    exact pow_nonneg hp0 _
  push Not at hz
  let rdφ : (Fin n → R) → (Fin n → K) := fun v j => φ (v j)
  have hword : ∀ i < N, ∀ j, dd (fun y : R => F.eval y) (Δ i j) (M.symm (Δ (i + 1)) j) ≠ 0 := by
    intro i hi j h0
    apply hz i (mem_range.mpr hi)
    have hpi : dd (fun x : Fin n → R => fun j => F.eval (x j)) (Δ i) (M.symm (Δ (i + 1))) =
        ∏ j, dd (fun y : R => F.eval y) (Δ i j) (M.symm (Δ (i + 1)) j) :=
      dd_pi (fun y : R => F.eval y) _ _
    rw [hpi]
    exact prod_eq_zero (mem_univ j) h0
  have hV : ∀ i, i ≤ N → ∀ j, V (Δ i j) := by
    intro i
    induction i with
    | zero => intro _; exact hΔV
    | succ i ih =>
      intro hi j
      have hβ : ∀ j, V (M.symm (Δ (i + 1)) j) :=
        fun j => hVS _ _ (ih (by omega) j) (hword i (by omega) j)
      have := hVM _ hβ j
      simpa using this
  have hround : ∀ i < N, ∀ j, φ (M.symm (Δ (i + 1)) j) ≠ 0 ↔ φ (Δ i j) ≠ 0 :=
    fun i hi j => hφS _ _ (hV i (by omega) j) (hword i hi j)
  have hwt : ∀ i < N, wt (rdφ (M.symm (Δ (i + 1)))) = wt (rdφ (Δ i)) := by
    intro i hi
    unfold wt
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and, rdφ]
    exact hround i hi j
  have hMbar : ∀ i < N, Mbar (rdφ (M.symm (Δ (i + 1)))) = rdφ (Δ (i + 1)) := by
    intro i hi
    funext j
    have hβ : ∀ j, V (M.symm (Δ (i + 1)) j) :=
      fun j => hVS _ _ (hV i (by omega) j) (hword i hi j)
    have := hφM _ hβ j
    simp only [AddEquiv.apply_symm_apply] at this
    exact this.symm
  have hnz : ∀ i, i ≤ N → rdφ (Δ i) ≠ 0 := by
    intro i
    induction i with
    | zero =>
      intro _ h
      obtain ⟨j, hj⟩ := hΔ
      exact hj (congrFun h j)
    | succ i ih =>
      intro hi h
      have h1 : rdφ (M.symm (Δ (i + 1))) ≠ 0 := by
        intro h3
        apply ih (by omega)
        funext j
        by_contra hj
        exact ((hround i (by omega) j).mpr hj) (congrFun h3 j)
      apply h1
      apply hMinj
      rw [hMbar i (by omega)]
      exact h
  have hpair : ∀ i < N, B ≤ wt (rdφ (Δ i)) + wt (rdφ (Δ (i + 1))) := by
    intro i hi
    have h1 : rdφ (M.symm (Δ (i + 1))) ≠ 0 := by
      intro h3
      apply hnz i (by omega)
      funext j
      by_contra hj
      exact ((hround i hi j).mpr hj) (congrFun h3 j)
    have := hB _ h1
    rwa [hwt i hi, hMbar i hi] at this
  have hk := sum_active_ge' (fun i => wt (rdφ (Δ i))) B N (fun i hi => hpair i (by omega))
  refine prod_le_pow_of_active N B
    (fun i => (dd (fun x : Fin n → R => fun j => F.eval (x j)) (Δ i) (M.symm (Δ (i + 1))) : ℚ) /
      Fintype.card (Fin n → R)) _ hp0 hp1 _ hk (fun i hi => ⟨by positivity, ?_⟩)
  have h := factor_le_gen F D (fun a => V a ∧ φ a ≠ 0) (fun a b ha => hD a b ha.1 ha.2)
    (Δ i) (M.symm (Δ (i + 1)))
  convert h using 2
  unfold wt
  apply congrArg Finset.card
  ext j
  simp only [mem_filter, mem_univ, true_and, rdφ]
  exact ⟨fun h => ⟨hV i (by omega) j, h⟩, fun h => h.2⟩

end Markov

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- the top layer: `δ_F(2^(k−1) u, β) ≤ 2 q^(k−1)` -/
theorem top_layer_le (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ : K)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b → b = a ∨ b = a + ρ)
    (u β : R) (hu : S.π u ≠ 0) :
    delta f (2 ^ (S.k - 1) * u) β ≤ 2 * Fintype.card K ^ (S.k - 1) := by
  have hk := S.hk
  have hval : ∀ x, f.eval (x + 2 ^ (S.k - 1) * u) - f.eval x = 2 ^ (S.k - 1) * u * f.derivative.eval x := by
    intro x
    obtain ⟨Q, hQ⟩ := taylor2 f x (2 ^ (S.k - 1) * u)
    have : (2 ^ (S.k - 1) * u) ^ 2 = (0 : R) := S.two_pow_mul_sq_eq_zero (S.k - 1) (by omega) u
    rw [hQ, this]; ring
  by_cases h0 : delta f (2 ^ (S.k - 1) * u) β = 0
  · rw [h0]; exact Nat.zero_le _
  obtain ⟨x0, hx0⟩ : ∃ x0, f.eval (x0 + 2 ^ (S.k - 1) * u) - f.eval x0 = β := by
    by_contra hne
    push Not at hne
    apply h0
    unfold delta
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    exact hne x hx
  unfold delta
  have hsub : univ.filter (fun x : R => f.eval (x + 2 ^ (S.k - 1) * u) - f.eval x = β) ⊆
      univ.filter (fun x : R => S.π x = S.π x0) ∪ univ.filter (fun x : R => S.π x = S.π x0 + ρ) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    rw [hval] at hx hx0
    have h1 : 2 ^ (S.k - 1) * u * (f.derivative.eval x - f.derivative.eval x0) = 0 := by
      rw [mul_sub, hx, hx0, sub_self]
    obtain ⟨v, hv⟩ := S.unit_ann (S.k - 1) (by omega) u _ hu h1
    have h2 : S.π (f.derivative.eval x - f.derivative.eval x0) = 0 := by
      rw [hv, show S.k - (S.k - 1) = 1 by omega, pow_one]; exact S.pi_two_mul _
    rw [map_sub, sub_eq_zero, S.pi_deriv_eval, S.pi_deriv_eval] at h2
    rcases hd2 _ _ h2.symm with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc _ ≤ (univ.filter (fun x : R => S.π x = S.π x0) ∪
        univ.filter (fun x : R => S.π x = S.π x0 + ρ)).card := Finset.card_le_card hsub
    _ ≤ (univ.filter (fun x : R => S.π x = S.π x0)).card +
        (univ.filter (fun x : R => S.π x = S.π x0 + ρ)).card := Finset.card_union_le _ _
    _ = 2 * Fintype.card K ^ (S.k - 1) := by rw [S.card_fiber hcard, S.card_fiber hcard]; ring

end GRS

namespace Markov

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

open scoped Classical in
/-- **Characteristics in layer `s ≥ 1`.** All words of `Δ 0` lie in `2^s R`, one of them in
`2^s R \ 2^(s+1) R`; `p'` has no zero; rows of the layer are bounded by `D`. -/
theorem char_prob_le_layer (S0 : APN2.GRS R K) {n : ℕ} (F : R[X]) (M : (Fin n → R) ≃+ (Fin n → R))
    (Δ : ℕ → (Fin n → R)) (N D B s : ℕ) (hs1 : 1 ≤ s) (hsk : s < S0.k)
    (hp' : ∀ a, (F.map S0.π).derivative.eval a ≠ 0)
    (hD : ∀ y b : R, S0.π y ≠ 0 → APN2.GRS.delta F (2 ^ s * y) b ≤ D) (hDR : D ≤ Fintype.card R)
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hΔV : ∀ j, ∃ y, Δ 0 j = 2 ^ s * y) (hΔ : ∃ j y, Δ 0 j = 2 ^ s * y ∧ S0.π y ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => F.eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤ ((D : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  have hrk := res_ker S0 M Mbar hM
  -- the transition of one word
  have hstep : ∀ a b : R, (∃ y, a = 2 ^ s * y) → dd (fun y : R => F.eval y) a b ≠ 0 →
      ∃ x, F.eval (x + a) - F.eval x = b := by
    intro a b _ h
    obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h)
    exact ⟨x, hx⟩
  apply char_prob_le_digit F M Δ N D B (fun w => ∃ y, w = 2 ^ s * y) (S0.digit s) Mbar
  · -- the S-box keeps the layer
    rintro a b ⟨y, rfl⟩ h
    obtain ⟨x, rfl⟩ := hstep _ _ ⟨y, rfl⟩ h
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
    rintro a b ⟨y, rfl⟩ h
    obtain ⟨x, rfl⟩ := hstep _ _ ⟨y, rfl⟩ h
    obtain ⟨Q, hQ⟩ := taylor2 F x (2 ^ s * y)
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
  · -- `M̄` is injective
    intro u hu
    have := hrk (fun i => S0.L (u i)) (by
      funext j
      show S0.π (M _ j) = 0
      rw [hM]
      simp only [S0.pi_L]
      rw [hu]; rfl)
    funext i
    have h := congrFun this i
    simp only [rd, S0.pi_L, Pi.zero_apply] at h
    exact h
  · exact hB
  · rintro a b ⟨y, rfl⟩ hy
    rw [S0.digit_eq s hsk] at hy
    exact hD y b hy
  · exact hDR
  · exact hΔV
  · obtain ⟨j, y, hj, hy⟩ := hΔ
    exact ⟨j, by rw [hj, S0.digit_eq s hsk]; exact hy⟩

end Markov


namespace Markov

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- `p'` of the family has no zero -/
theorem p5_deriv_ne {K : Type*} [Field K] [CharP K 2] [Fintype K] (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r)
    (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (x : K) : (F5 K m r).derivative.eval x ≠ 0 := by
  rw [p5_deriv m r (by omega) (by omega), ← p5_hasse2 m r hm hr x]
  exact p5_hasse2_ne m r hm hr hodd hcard x

open scoped Classical in
/-- **Lower-layer characteristics for `F♯` (`r ≥ 5`).** If all words of `Δ 0` lie in `2^s R` and one lies in
`2^s R \ 2^(s+1) R`, then the probability is at most `(q^(s+1)/q^k)^(B ⌊N/2⌋)` for `1 ≤ s ≤ k−2`. -/
theorem char_prob_le_fam5_layer (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Δ : ℕ → (Fin n → R)) (N B s : ℕ) (hs1 : 1 ≤ s)
    (hsk : s + 2 ≤ S0.k)
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hΔV : ∀ j, ∃ y, Δ 0 j = 2 ^ s * y) (hΔ : ∃ j y, Δ 0 j = 2 ^ s * y ∧ S0.π y ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤
      (((Fintype.card K ^ (s + 1) : ℕ) : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  haveI := S0.charP2
  apply char_prob_le_layer S0 _ M Δ N _ B s hs1 (by omega)
  · rw [S0.fam5_sh_map]; exact p5_deriv_ne m r hm5 hr5 hmodd hm
  · intro y b hy
    rcases S0.fam5_interfamily hcard m r hm5 hr5 hrm hodd hmodd hm hcop s hs1 hsk y b hy with h | h
    · rw [h]; exact Nat.zero_le _
    · exact h.le
  · rw [hcard]; exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  · exact hM
  · exact hB
  · exact hΔV
  · exact hΔ

open scoped Classical in
/-- **Top-layer characteristics** (any lift with `p'` zero-free and two-to-one): probability
`≤ (2 q^(k−1)/q^k)^(B ⌊N/2⌋) = (2/q)^(B ⌊N/2⌋)`. -/
theorem char_prob_le_top (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (F : R[X]) (ρ : K)
    (hd2 : ∀ a b : K, (F.map S0.π).derivative.eval a = (F.map S0.π).derivative.eval b → b = a ∨ b = a + ρ)
    (hp' : ∀ a, (F.map S0.π).derivative.eval a ≠ 0) (hq2 : 2 ≤ Fintype.card K)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Δ : ℕ → (Fin n → R)) (N B : ℕ)
    (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (hΔV : ∀ j, ∃ y, Δ 0 j = 2 ^ (S0.k - 1) * y)
    (hΔ : ∃ j y, Δ 0 j = 2 ^ (S0.k - 1) * y ∧ S0.π y ≠ 0) :
    (Fintype.card {v // trail (fun x : Fin n → R => fun j => F.eval (x j)) M Δ N v} : ℚ) /
        Fintype.card (Fin (N + 1) → (Fin n → R)) ≤
      (((2 * Fintype.card K ^ (S0.k - 1) : ℕ) : ℚ) / Fintype.card R) ^ (B * (N / 2)) := by
  have hk := S0.hk
  apply char_prob_le_layer S0 F M Δ N _ B (S0.k - 1) (by omega) (by omega) hp'
  · intro y b hy; exact S0.top_layer_le hcard F ρ hd2 y b hy
  · rw [hcard]
    calc 2 * Fintype.card K ^ (S0.k - 1) ≤ Fintype.card K * Fintype.card K ^ (S0.k - 1) :=
          Nat.mul_le_mul_right _ hq2
      _ = Fintype.card K ^ S0.k := by rw [← pow_succ']; congr 1; omega
  · exact hM
  · exact hB
  · exact hΔV
  · exact hΔ

end Markov

end APN2

#print axioms APN2.Markov.char_prob_le_digit
#print axioms APN2.GRS.top_layer_le
#print axioms APN2.Markov.char_prob_le_layer
#print axioms APN2.Markov.char_prob_le_fam5_layer
#print axioms APN2.Markov.char_prob_le_top
