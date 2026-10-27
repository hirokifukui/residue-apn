import Apn2R03.HullProb
import Apn2R03.ResPerm

/-!
# Differentials and fixed keys for `F♯` over `GR(2^k, m)` (Claude, 2026-10-26, R05c)

* `exists_layer`, `exists_layer_vec` : every nonzero element (vector) has a 2-adic layer;
* `branch_lift` : a branch number `B` of `M̄` over `F_q` is a branch number of `M` over `R` (nonzero words);
* `fam5_dp_le`  : every row of `F♯` (`r ≥ 5`) with nonzero input has entries `≤ 2 q^(k−1)` (`DP ≤ 2/q`);
* `fam5_bij`    : `F♯` permutes `R`;
* `fam5_diff2`  : every two-round differential of the SPN with S-box `F♯` and linear layer of residue branch
                  number `B` has probability `≤ (2q^(k−1)/q^k)^(B−1) = (2/q)^(B−1)`;
* `fam5_fixed_key` : the corresponding fixed-key statement.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

theorem exists_layer (u : R) (hu : u ≠ 0) : ∃ s, s < S.k ∧ ∃ y, u = 2 ^ s * y ∧ S.π y ≠ 0 := by
  by_contra h
  push Not at h
  have hall : ∀ t, t ≤ S.k → ∃ y, u = 2 ^ t * y := by
    intro t
    induction t with
    | zero => intro _; exact ⟨u, by ring⟩
    | succ t ih =>
      intro ht
      obtain ⟨y, hy⟩ := ih (by omega)
      obtain ⟨y', hy'⟩ := (S.ker2 y).mp (h t (by omega) y hy)
      exact ⟨y', by rw [hy, hy', pow_succ]; ring⟩
  obtain ⟨y, hy⟩ := hall S.k le_rfl
  exact hu (by rw [hy, S.nil, zero_mul])

theorem exists_layer_vec {n : ℕ} (x : Fin n → R) (hx : x ≠ 0) :
    ∃ s, s < S.k ∧ (∀ j, ∃ y, x j = 2 ^ s * y) ∧ ∃ j y, x j = 2 ^ s * y ∧ S.π y ≠ 0 := by
  by_contra h
  push Not at h
  have hall : ∀ t, t ≤ S.k → ∀ j, ∃ y, x j = 2 ^ t * y := by
    intro t
    induction t with
    | zero => intro _ j; exact ⟨x j, by ring⟩
    | succ t ih =>
      intro ht j
      obtain ⟨y, hy⟩ := ih (by omega) j
      obtain ⟨y', hy'⟩ := (S.ker2 y).mp (h t (by omega) (ih (by omega)) j y hy)
      exact ⟨y', by rw [hy, hy', pow_succ]; ring⟩
  apply hx
  funext j
  obtain ⟨y, hy⟩ := hall S.k le_rfl j
  rw [hy, S.nil, zero_mul]; rfl

theorem two_pow_mul_ne_zero (s : ℕ) (hs : s < S.k) (y : R) (hy : S.π y ≠ 0) : (2 : R) ^ s * y ≠ 0 := by
  intro h
  obtain ⟨z, hz⟩ := S.ann_two_pow s (S.k - s) (by omega) y h
  apply hy
  rw [hz]; exact S.pi_two_pow_mul _ (by omega) _

end GRS

namespace Markov

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

open scoped Classical in
/-- the residue branch number is a branch number over `R` -/
theorem branch_lift (S0 : APN2.GRS R K) {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R))
    (Mbar : (Fin n → K) → (Fin n → K)) (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u)) :
    ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x) := by
  intro x hx
  obtain ⟨s, hs, hall, j0, y0, hj0, hy0⟩ := S0.exists_layer_vec x hx
  choose Y hY using hall
  have hxY : x = (2 ^ s : ℕ) • Y := by funext i; simp [hY i, nsmul_eq_mul]
  have hMx : ∀ j, M x j = 2 ^ s * M Y j := by intro j; rw [hxY, map_nsmul]; simp [nsmul_eq_mul]
  set u : Fin n → K := fun i => S0.π (Y i)
  have hu : u ≠ 0 := by
    intro h
    have := congrFun h j0
    simp only [u, Pi.zero_apply] at this
    apply hy0
    have e : (2 : R) ^ s * (y0 - Y j0) = 0 := by rw [mul_sub, ← hj0, ← hY j0, sub_self]
    obtain ⟨z, hz⟩ := S0.ann_two_pow s (S0.k - s) (by omega) _ e
    have h2 : S0.π (y0 - Y j0) = 0 := by rw [hz]; exact S0.pi_two_pow_mul _ (by omega) _
    rw [map_sub, this, sub_zero] at h2
    exact h2
  have h1 : wt u ≤ wtG x := by
    unfold wt wtG
    apply Finset.card_le_card
    intro j hj
    simp only [mem_filter, mem_univ, true_and, u] at hj ⊢
    rw [hY j]
    exact S0.two_pow_mul_ne_zero s hs _ hj
  have h2 : wt (Mbar u) ≤ wtG (M x) := by
    unfold wt wtG
    apply Finset.card_le_card
    intro j hj
    simp only [mem_filter, mem_univ, true_and, u] at hj ⊢
    rw [hMx j]
    apply S0.two_pow_mul_ne_zero s hs
    rw [hM]; exact hj
  have := hB u hu
  omega

end Markov

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- every row with nonzero input of `F♯` has entries `≤ 2 q^(k−1)` -/
theorem fam5_dp_le (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (α β : R) (hα : α ≠ 0) :
    delta (Fsh5 R m r) α β ≤ 2 * Fintype.card K ^ (S.k - 1) := by
  haveI := S.charP2
  have hk := S.hk
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  obtain ⟨s, hs, y, rfl, hy⟩ := S.exists_layer α hα
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · have h := (S.fam5_units' hcard m r hm5 hr5 hrm hodd hmodd hm hcop (2 ^ 0 * y) β
      (by rw [pow_zero, one_mul]; exact hy)).1
    calc _ ≤ 2 * Fintype.card K := h
      _ = 2 * Fintype.card K ^ 1 := by rw [pow_one]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq1 (by omega))
  · rcases Nat.lt_or_ge (s + 1) S.k with hlt | hge
    · rcases S.fam5_interfamily hcard m r hm5 hr5 hrm hodd hmodd hm hcop s hs1 (by omega) y β hy with h | h
      · rw [h]; exact Nat.zero_le _
      · rw [h]
        calc Fintype.card K ^ (s + 1) ≤ Fintype.card K ^ (S.k - 1) := Nat.pow_le_pow_right hq1 (by omega)
          _ ≤ _ := Nat.le_mul_of_pos_left _ (by norm_num)
    · have hsk : s = S.k - 1 := by omega
      subst hsk
      have hd2 := (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).2
      have hmap := S.fam5_sh_map (R := R) m r
      have hd2' : ∀ a b : K, ((Fsh5 R m r).map S.π).derivative.eval a =
          ((Fsh5 R m r).map S.π).derivative.eval b → b = a ∨ b = a + 1 := by
        rw [hmap, ← F5_map S.π m r]; exact hd2
      exact S.top_layer_le hcard (Fsh5 R m r) 1 hd2' y β hy

include S in
/-- `F♯` permutes `R` -/
theorem fam5_bij (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (_hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) :
    Function.Bijective (fun x : R => (Fsh5 R m r).eval x) := by
  haveI := S.charP2
  rw [← Finite.injective_iff_bijective]
  intro x x' hxx
  by_contra hne
  have hα : x' - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨s, hs, y, hy, hyπ⟩ := S.exists_layer (x' - x) hα
  have hx' : x' = x + 2 ^ s * y := by rw [← hy]; ring
  simp only at hxx
  rw [hx'] at hxx
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · have hinj := resPerm5 m r hm5 hr5 hmodd hm hcop hodd
    have := congrArg S.π hxx
    rw [S.pi_eval, S.pi_eval, S.fam5_sh_map, map_add, pow_zero, one_mul] at this
    have := hinj this
    apply hyπ
    linear_combination -this
  · obtain ⟨Q, hQ⟩ := taylor2 (Fsh5 R m r) x (2 ^ s * y)
    have e : (Fsh5 R m r).eval (x + 2 ^ s * y) - (Fsh5 R m r).eval x =
        2 ^ s * (y * (Fsh5 R m r).derivative.eval x + 2 ^ s * (y ^ 2 * Q)) := by rw [hQ]; ring
    rw [hxx, sub_self] at e
    apply S.two_pow_mul_ne_zero s hs _ _ e.symm
    rw [map_add, map_mul, S.pi_two_pow_mul s hs1, add_zero, S.pi_deriv_eval, S.fam5_sh_map]
    refine mul_ne_zero hyπ ?_
    exact APN2.Markov.p5_deriv_ne m r hm5 hr5 hmodd hm _

end GRS

namespace Markov

variable {R K : Type*} [CommRing R] [Field K] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- **Two-round differentials of the SPN with S-box `F♯` (`r ≥ 5`).** -/
theorem fam5_diff2 (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (a b : Fin n → R) (ha : a ≠ 0) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤
      (((2 * Fintype.card K ^ (S0.k - 1) : ℕ) : ℚ) / Fintype.card R) ^ (B - 1) := by
  apply diff2_prob_le (fun x : R => (APN2.Fsh5 R m r).eval x)
    (S0.fam5_bij m r hm5 hr5 hrm hodd hmodd hm hcop) M B hB1 (branch_lift S0 M Mbar hM B hB)
  · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Fintype.card_pos.le)
  · intro u v hu
    unfold DP
    apply div_le_div_of_nonneg_right _ (by exact_mod_cast Fintype.card_pos.le)
    rw [dd_eq_delta]
    exact_mod_cast S0.fam5_dp_le hcard m r hm5 hr5 hrm hodd hmodd hm hcop u v hu
  · exact ha

/-- **Fixed keys** for `F♯`. -/
theorem fam5_fixed_key (S0 : APN2.GRS R K) (hcard : Fintype.card R = Fintype.card K ^ S0.k)
    (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    {n : ℕ} (M : (Fin n → R) ≃+ (Fin n → R)) (Mbar : (Fin n → K) → (Fin n → K))
    (hM : ∀ v j, S0.π (M v j) = Mbar (fun i => S0.π (v i)) j)
    (B : ℕ) (hB1 : 1 ≤ B) (hB : ∀ u : Fin n → K, u ≠ 0 → B ≤ wt u + wt (Mbar u))
    (a b : Fin n → R) (ha : a ≠ 0) (t : ℚ) (ht : 0 < t) :
    ((univ.filter (fun κ : (Fin n → R) × (Fin n → R) =>
        t ≤ ((univ.filter (fun x0 : Fin n → R =>
          out2 (fun x : Fin n → R => fun j => (APN2.Fsh5 R m r).eval (x j)) M a x0 κ.1 κ.2 = b)).card : ℚ) /
            Fintype.card (Fin n → R))).card : ℚ) / Fintype.card ((Fin n → R) × (Fin n → R)) ≤
      (((2 * Fintype.card K ^ (S0.k - 1) : ℕ) : ℚ) / Fintype.card R) ^ (B - 1) / t :=
  fixed_key_markov _ M a b t ht _ (fam5_diff2 S0 hcard m r hm5 hr5 hrm hodd hmodd hm hcop M Mbar hM B hB1 hB a b ha)

end Markov

end APN2

#print axioms APN2.Markov.branch_lift
#print axioms APN2.GRS.fam5_dp_le
#print axioms APN2.GRS.fam5_bij
#print axioms APN2.Markov.fam5_diff2
#print axioms APN2.Markov.fam5_fixed_key
