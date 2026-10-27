import Apn2R03.Hull

/-!
# Two-round differentials: probability and fixed keys (Claude, 2026-10-26, R05c)

Two rounds `x ↦ M(S x) + κ` on a finite abelian group `G`, a uniform start `x₀` and uniform keys `κ₁, κ₂`.
`out2 a x₀ κ₁ κ₂` is the output difference of the pair `(x₀, x₀ + a)`.
* `card_out2`     : `#{(x₀,κ₁,κ₂) : out2 = b} = |G| · Σ_x dd(a, x) · dd(M x, M⁻¹ b)`;
* `diff2_prob_le` : for the wordwise S-box layer on `R^n` and a layer of branch number `B` over `R`,
                    the probability of every two-round differential with `a ≠ 0` is `≤ p^(B−1)`;
* `fixed_key_le`  : for every `t > 0`, the proportion of key pairs whose fixed-key probability is `≥ t` is
                    `≤ p^(B−1)/t`.
-/

set_option linter.unusedSectionVars false

namespace APN2.Markov

open Finset

section prob
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- output difference after two rounds -/
def out2 (S : G → G) (M : G ≃+ G) (a x0 κ1 κ2 : G) : G :=
  (M (S (M (S (x0 + a)) + κ1)) + κ2) - (M (S (M (S x0) + κ1)) + κ2)

theorem out2_iff (S : G → G) (M : G ≃+ G) (a b x0 κ1 κ2 : G) :
    out2 S M a x0 κ1 κ2 = b ↔
      S ((M (S x0) + κ1) + M (S (x0 + a) - S x0)) - S (M (S x0) + κ1) = M.symm b := by
  have e : M (S (x0 + a)) + κ1 = (M (S x0) + κ1) + M (S (x0 + a) - S x0) := by
    rw [map_sub]; abel
  unfold out2
  rw [e, add_sub_add_right_eq_sub, ← map_sub]
  constructor
  · intro h; rw [← h, AddEquiv.symm_apply_apply]
  · intro h; rw [h, AddEquiv.apply_symm_apply]

theorem dd_eq_sum (S : G → G) (u v : G) :
    (dd S u v : ℚ) = ∑ y : G, if S (y + u) - S y = v then (1 : ℚ) else 0 := by
  unfold dd
  rw [Fintype.card_subtype, Finset.card_filter]
  push_cast; rfl

open scoped Classical in
theorem card_out2 (S : G → G) (M : G ≃+ G) (a b : G) :
    ((univ.filter (fun t : G × G × G => out2 S M a t.1 t.2.1 t.2.2 = b)).card : ℚ) =
      Fintype.card G * ∑ x : G, (dd S a x : ℚ) * dd S (M x) (M.symm b) := by
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  -- the last key is free
  have h1 : ∀ x0 κ1 : G, (∑ κ2 : G, if out2 S M a x0 κ1 κ2 = b then (1 : ℚ) else 0) =
      Fintype.card G * (if S ((M (S x0) + κ1) + M (S (x0 + a) - S x0)) - S (M (S x0) + κ1) = M.symm b
        then 1 else 0) := by
    intro x0 κ1
    simp only [out2_iff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [h1, ← Finset.mul_sum]
  congr 1
  -- the first key: shift `κ₁ ↦ y = M(S x₀) + κ₁`
  have h2 : ∀ x0 : G, (∑ κ1 : G, if S ((M (S x0) + κ1) + M (S (x0 + a) - S x0)) - S (M (S x0) + κ1) =
      M.symm b then (1 : ℚ) else 0) = dd S (M (S (x0 + a) - S x0)) (M.symm b) := by
    intro x0
    rw [dd_eq_sum]
    exact Fintype.sum_equiv (Equiv.addLeft (M (S x0))) _ _ (fun κ1 => rfl)
  simp only [h2]
  -- group the starting states by the first output difference
  rw [← Finset.sum_fiberwise (s := (univ : Finset G)) (g := fun x0 => S (x0 + a) - S x0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_congr rfl (fun x0 hx0 => by rw [(Finset.mem_filter.mp hx0).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  unfold dd
  rw [Fintype.card_subtype]

/-- the two-round differential probability as a sum over the middle difference -/
theorem prob_out2 (S : G → G) (M : G ≃+ G) (a b : G) :
    ((univ.filter (fun t : G × G × G => out2 S M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card (G × G × G) =
      ∑ x : G, ((dd S a x : ℚ) / Fintype.card G) * ((dd S (M x) (M.symm b) : ℚ) / Fintype.card G) := by
  have hG : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  rw [card_out2, Fintype.card_prod, Fintype.card_prod]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  field_simp

/-- Markov's inequality for fixed keys (generic form) -/
theorem fixed_key_markov (S : G → G) (M : G ≃+ G) (a b : G) (t : ℚ) (ht : 0 < t) (P : ℚ)
    (hP : ((univ.filter (fun t : G × G × G => out2 S M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card (G × G × G) ≤ P) :
    ((univ.filter (fun κ : G × G =>
        t ≤ ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) / Fintype.card G)).card : ℚ) /
      Fintype.card (G × G) ≤ P / t := by
  have hG : (0 : ℚ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hGG : (0 : ℚ) < Fintype.card (G × G) := by exact_mod_cast Fintype.card_pos
  have hc : ((univ.filter (fun t : G × G × G => out2 S M a t.1 t.2.1 t.2.2 = b)).card : ℚ) =
      ∑ κ : G × G, ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) := by
    rw [Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro κ _
    rw [Finset.card_filter]
    push_cast
    rfl
  have havg : (∑ κ : G × G, ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) /
        Fintype.card G) / Fintype.card (G × G) ≤ P := by
    rw [← Finset.sum_div, div_div, ← hc]
    have e : (Fintype.card G : ℚ) * Fintype.card (G × G) = Fintype.card (G × G × G) := by
      rw [Fintype.card_prod G (G × G)]; push_cast; ring
    rw [e]; exact hP
  have hnn : ∀ κ : G × G, 0 ≤ ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) /
      Fintype.card G := fun κ => div_nonneg (Nat.cast_nonneg _) hG.le
  have hmk : t * ((univ.filter (fun κ : G × G =>
      t ≤ ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) / Fintype.card G)).card : ℚ) ≤
      ∑ κ : G × G, ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) / Fintype.card G := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    calc _ ≤ ∑ κ ∈ univ.filter (fun κ : G × G =>
          t ≤ ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) / Fintype.card G),
          ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) / Fintype.card G :=
          Finset.sum_le_sum (fun κ hκ => (Finset.mem_filter.mp hκ).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun κ _ _ => hnn κ)
  rw [le_div_iff₀ ht]
  calc _ = t * ((univ.filter (fun κ : G × G =>
        t ≤ ((univ.filter (fun x0 : G => out2 S M a x0 κ.1 κ.2 = b)).card : ℚ) / Fintype.card G)).card : ℚ) /
          Fintype.card (G × G) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hmk hGG.le
    _ ≤ P := havg

end prob

section words
variable {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]

theorem dd_word (s : R → R) {n : ℕ} (u v : Fin n → R) :
    (dd (fun x : Fin n → R => fun j => s (x j)) u v : ℚ) / Fintype.card (Fin n → R) =
      ∏ j, DP s (u j) (v j) := by
  rw [dd_pi, Nat.cast_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  unfold DP
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Two-round differentials.** -/
theorem diff2_prob_le {n : ℕ} (s : R → R) (hs : Function.Bijective s)
    (M : (Fin n → R) ≃+ (Fin n → R)) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x))
    (p : ℚ) (hp0 : 0 ≤ p) (hp : ∀ u v : R, u ≠ 0 → DP s u v ≤ p)
    (a b : Fin n → R) (ha : a ≠ 0) :
    ((univ.filter (fun t : (Fin n → R) × (Fin n → R) × (Fin n → R) =>
        out2 (fun x : Fin n → R => fun j => s (x j)) M a t.1 t.2.1 t.2.2 = b)).card : ℚ) /
        Fintype.card ((Fin n → R) × (Fin n → R) × (Fin n → R)) ≤ p ^ (B - 1) := by
  rw [prob_out2]
  simp only [dd_word]
  exact hull2_le s hs M B hB1 hB p hp0 hp a (M.symm b) ha

/-- **Fixed keys** (Markov's inequality): at most a proportion `p^(B−1)/t` of the key pairs give the
differential a fixed-key probability `≥ t`. -/
theorem fixed_key_le {n : ℕ} (s : R → R) (hs : Function.Bijective s)
    (M : (Fin n → R) ≃+ (Fin n → R)) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ x : Fin n → R, x ≠ 0 → B ≤ wtG x + wtG (M x))
    (p : ℚ) (hp0 : 0 ≤ p) (hp : ∀ u v : R, u ≠ 0 → DP s u v ≤ p)
    (a b : Fin n → R) (ha : a ≠ 0) (t : ℚ) (ht : 0 < t) :
    ((univ.filter (fun κ : (Fin n → R) × (Fin n → R) =>
        t ≤ ((univ.filter (fun x0 : Fin n → R =>
          out2 (fun x : Fin n → R => fun j => s (x j)) M a x0 κ.1 κ.2 = b)).card : ℚ) /
            Fintype.card (Fin n → R))).card : ℚ) / Fintype.card ((Fin n → R) × (Fin n → R)) ≤
      p ^ (B - 1) / t :=
  fixed_key_markov _ M a b t ht _ (diff2_prob_le s hs M B hB1 hB p hp0 hp a b ha)

end words

end APN2.Markov

#print axioms APN2.Markov.card_out2
#print axioms APN2.Markov.diff2_prob_le
#print axioms APN2.Markov.fixed_key_le
