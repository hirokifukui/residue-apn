import Apn2R03.GRInst

/-!
# The residue APN property of P_{m,r}, proved (Claude, 2026-10-25, R04-08)

Earlier paper (arXiv:2610.21178, Thm 3.1): P_{m,r} = σ^{m-2} ∘ X³ ∘ T_r with T_r = Σ_{i<r} X^{2^i}.
Here we do not compose with σ^{m-2}: we use the additive map
  Y(x) = Σ_{i<r-2} x^{2^i} + x^{2^{m-2}} + x^{2^{m-1}}   ( = T_r(x)^{2^{m-2}} on F_q ),
and prove, over K with |K| = 2^m,
* `p3_cube`, `p5_cube` : P_{m,r}(x) = Y(x)³ (evaluation identity);
* `Y_add`              : Y is additive;
* `S_inj`, `Y3_inj`, `Y5_inj` : Y(x) = 0 ⇒ x = 0 (uses Y⁴ = T_r, T_r + T_r² = x + x^{2^r},
                         gcd(r, m) = 1 and r odd);
* `resAPN_of_cube`     : an additive injective Y makes Y³ APN in every nonzero direction;
* `resAPN3`, `resAPN5` : `ResAPN (Fnat3 K m)`, `ResAPN (F5 K m r)` — no hypothesis left;
* `fam3_units'`, `fam5_units'` : Theorem A on all unit directions without `hAPN`.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

section cube
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- an additive injective `Y` makes `p = Y³` APN in every nonzero direction (needs 3 ≠ 0) -/
theorem resAPN_of_cube (p : K[X]) (Y : K → K) (hadd : ∀ x y, Y (x + y) = Y x + Y y)
    (hinj : ∀ x, Y x = 0 → x = 0) (hp : ∀ x, p.eval x = Y x ^ 3) (h3 : (3 : K) ≠ 0)
    (c : K) (hc : c ≠ 0) (b : K) :
    (univ.filter (fun t : K => p.eval (t + c) - p.eval t = b)).card ≤ 2 := by
  have hsub : ∀ x y, Y (x - y) = Y x - Y y := by
    intro x y
    have h := hadd (x - y) y
    rw [sub_add_cancel] at h
    linear_combination -h
  have hd : Y c ≠ 0 := fun h => hc (hinj c h)
  by_cases hne : (univ.filter (fun t : K => p.eval (t + c) - p.eval t = b)).Nonempty
  · obtain ⟨t0, ht0⟩ := hne
    simp only [mem_filter, mem_univ, true_and] at ht0
    have hsubset : univ.filter (fun t : K => p.eval (t + c) - p.eval t = b) ⊆ {t0, -t0 - c} := by
      intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      simp only [hp, hadd] at ht ht0
      have key : 3 * Y c * (Y t - Y t0) * (Y t + Y t0 + Y c) = 0 := by
        linear_combination ht - ht0
      rcases mul_eq_zero.mp key with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' h3
          · exact absurd h'' hd
        · have e : t - t0 = 0 := hinj _ (by rw [hsub]; exact h')
          rw [sub_eq_zero.mp e]
          simp
      · have e : t + t0 + c = 0 := hinj _ (by rw [hadd, hadd]; exact h)
        simp only [mem_insert, mem_singleton]
        right
        linear_combination e
    exact (card_le_card hsubset).trans (card_insert_le _ _ |>.trans (by simp))
  · rw [not_nonempty_iff_eq_empty.mp hne]; simp

end cube

section frob
variable {K : Type*} [Field K] [CharP K 2]

theorem sum_sq_char2 (s : Finset ℕ) (f : ℕ → K) : (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [sum_insert ha, sum_insert ha, add_sq, ih]
  have h2 : (2 : K) = 0 := two_K
  rw [h2]; ring

theorem sum_frob_add (s : Finset ℕ) (x y : K) :
    ∑ i ∈ s, (x + y) ^ (2 ^ i) = ∑ i ∈ s, x ^ (2 ^ i) + ∑ i ∈ s, y ^ (2 ^ i) := by
  rw [← sum_add_distrib]
  exact sum_congr rfl (fun i _ => frob_add i x y)

theorem sq_two_pow (x : K) (i : ℕ) : (x ^ (2 ^ i)) ^ 2 = x ^ (2 ^ (i + 1)) := by
  rw [← pow_mul, pow_succ]

/-- `T_n(x)² = T_n(x) + x + x^{2^n}` in characteristic 2 -/
theorem trsum_sq (n : ℕ) (x : K) :
    (∑ i ∈ range n, x ^ (2 ^ i)) ^ 2 = ∑ i ∈ range n, x ^ (2 ^ i) + x + x ^ (2 ^ n) := by
  rw [sum_sq_char2]
  simp_rw [sq_two_pow]
  have h1 := Finset.sum_range_succ' (fun i => x ^ (2 ^ i)) n
  have h2 := Finset.sum_range_succ (fun i => x ^ (2 ^ i)) n
  simp only [pow_zero, pow_one] at h1
  have hh : (2 : K) = 0 := two_K
  linear_combination h2 - h1 - x * hh

/-- `T_r` has trivial kernel when `r` is odd and `gcd(r, m) = 1` -/
theorem S_inj [Fintype K] (m r : ℕ) (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m)
    (hodd : Odd r) (x : K) (hS : ∑ i ∈ range r, x ^ (2 ^ i) = 0) : x = 0 := by
  have hq : x ^ (2 ^ m) = x := by rw [← hcard, FiniteField.pow_card]
  have hsq := trsum_sq r x
  rw [hS] at hsq
  have hh : (2 : K) = 0 := two_K
  have hr : x ^ (2 ^ r) = x := by linear_combination -hsq - x * hh
  have h1 := frob_gcd x r m hr hq
  rw [hcop, pow_one] at h1
  have hx : x * (x - 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp hx with h | h
  · exact h
  · have e : x = 1 := sub_eq_zero.mp h
    rw [e] at hS
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hS
    rw [odd_cast_one r hodd] at hS
    exact absurd hS one_ne_zero

end frob

section family
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- the additive map for P_{m,3} -/
def Y3 (m : ℕ) (x : K) : K := x + x ^ (2 ^ (m - 2)) + x ^ (2 ^ (m - 1))

/-- the additive map for P_{m,r}, r ≥ 4 -/
def Y5 (m r : ℕ) (x : K) : K := ∑ i ∈ range (r - 2), x ^ (2 ^ i) + x ^ (2 ^ (m - 2)) + x ^ (2 ^ (m - 1))

theorem UV (m : ℕ) (hm : 3 ≤ m) (x : K) : (x ^ (2 ^ (m - 2))) ^ 2 = x ^ (2 ^ (m - 1)) := by
  rw [sq_two_pow]; congr 2; omega

theorem Vx (m : ℕ) (hm : 3 ≤ m) (hcard : Fintype.card K = 2 ^ m) (x : K) :
    (x ^ (2 ^ (m - 1))) ^ 2 = x := by
  rw [sq_two_pow, show m - 1 + 1 = m by omega, ← hcard, FiniteField.pow_card]

theorem Y3_add (m : ℕ) (x y : K) : Y3 m (x + y) = Y3 m x + Y3 m y := by
  unfold Y3; rw [frob_add, frob_add]; ring

theorem Y5_add (m r : ℕ) (x y : K) : Y5 m r (x + y) = Y5 m r x + Y5 m r y := by
  unfold Y5; rw [sum_frob_add, frob_add, frob_add]; ring

theorem p3_cube (m : ℕ) (hm : 3 ≤ m) (hcard : Fintype.card K = 2 ^ m) (x : K) :
    (Fnat3 K m).eval x = Y3 m x ^ 3 := by
  have hU := UV m hm x
  have hV := Vx m hm hcard x
  have h2 : (2 : K) = 0 := two_K
  rw [p3_eval]
  unfold Y3
  generalize x ^ (2 ^ (m - 2)) = U at hU ⊢
  generalize x ^ (2 ^ (m - 1)) = V at hU hV ⊢
  linear_combination (-U - 3 * V - 3 * x) * hU + (-3 * U - V - 3 * x - 3) * hV
    + (-3 * U * V * x - U * x ^ 2 - U * x - V * x ^ 2 - 2 * V * x - x ^ 2 - x) * h2

theorem p5_cube (m r : ℕ) (hm : 3 ≤ m) (hr : 4 ≤ r) (hcard : Fintype.card K = 2 ^ m) (x : K) :
    (F5 K m r).eval x = Y5 m r x ^ 3 := by
  have hU := UV m hm x
  have hV := Vx m hm hcard x
  have hT := trsum_sq (r - 2) x
  have h2 : (2 : K) = 0 := two_K
  rw [F5_eq_paper K m r hr]
  simp only [P5paper, T5, eval_add, eval_mul, eval_pow, eval_X, eval_finsetSum, pow_add]
  unfold Y5
  generalize ∑ i ∈ range (r - 2), x ^ (2 ^ i) = t at hT ⊢
  generalize x ^ (2 ^ (r - 2)) = W at hT ⊢
  generalize x ^ (2 ^ (m - 2)) = U at hU ⊢
  generalize x ^ (2 ^ (m - 1)) = V at hU hV ⊢
  linear_combination (-U - 3 * V - 3 * t) * hU + (-3 * U - V - 3 * t - 3) * hV
    + (-3 * U - 3 * V - t - 1) * hT
    + (-3 * U * V * t - U * W - U * t - 3 * U * x - V * W - 3 * V * t - 2 * V * x - 2 * t * x - 2 * x) * h2

theorem Y3_inj (m : ℕ) (hm : 3 ≤ m) (hcard : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m)
    (x : K) (hY : Y3 m x = 0) : x = 0 := by
  have hU := UV m hm x
  have hV := Vx m hm hcard x
  have h2 : (2 : K) = 0 := two_K
  apply S_inj m 3 hcard h3 (by decide) x
  have h4 : Y3 m x ^ 4 = x + x ^ 2 + x ^ 4 := by
    unfold Y3
    generalize x ^ (2 ^ (m - 2)) = U at hU ⊢
    generalize x ^ (2 ^ (m - 1)) = V at hU hV ⊢
    have e2 : (x + U + V) ^ 2 = x ^ 2 + V + x := by
      linear_combination hU + hV + (x * U + x * V + U * V) * h2
    rw [show (x + U + V) ^ 4 = ((x + U + V) ^ 2) ^ 2 by ring, e2]
    linear_combination hV + (x ^ 2 * V + x ^ 3 + V * x) * h2
  rw [hY] at h4
  simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one, zero_add]
  norm_num at h4 ⊢
  linear_combination -h4

theorem Y5_inj (m r : ℕ) (hm : 3 ≤ m) (hr : 4 ≤ r) (hcard : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (hodd : Odd r) (x : K) (hY : Y5 m r x = 0) : x = 0 := by
  have hU := UV m hm x
  have hV := Vx m hm hcard x
  have h2 : (2 : K) = 0 := two_K
  apply S_inj m r hcard hcop hodd x
  -- T_r(x) = x + x² + (T_{r-2}(x))⁴
  have hsplit : ∑ i ∈ range r, x ^ (2 ^ i) = x + x ^ 2 + (∑ i ∈ range (r - 2), x ^ (2 ^ i)) ^ 4 := by
    have e4 : (∑ i ∈ range (r - 2), x ^ (2 ^ i)) ^ 4 = ∑ i ∈ range (r - 2), x ^ (2 ^ (i + 2)) := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sum_sq_char2, sum_sq_char2]
      refine sum_congr rfl (fun i _ => ?_)
      rw [sq_two_pow, sq_two_pow]
    rw [e4, show r = (r - 2) + 1 + 1 by omega, sum_range_succ', sum_range_succ']
    simp only [pow_zero, pow_one, show r - 2 + 1 + 1 - 2 = r - 2 by omega]
    ring_nf
  have h4 : Y5 m r x ^ 4 = (∑ i ∈ range (r - 2), x ^ (2 ^ i)) ^ 4 + x + x ^ 2 := by
    unfold Y5
    generalize ∑ i ∈ range (r - 2), x ^ (2 ^ i) = t
    generalize x ^ (2 ^ (m - 2)) = U at hU ⊢
    generalize x ^ (2 ^ (m - 1)) = V at hU hV ⊢
    have e2 : (t + U + V) ^ 2 = t ^ 2 + V + x := by
      linear_combination hU + hV + (t * U + t * V + U * V) * h2
    rw [show (t + U + V) ^ 4 = ((t + U + V) ^ 2) ^ 2 by ring, e2]
    linear_combination hV + (t ^ 2 * V + t ^ 2 * x + V * x) * h2
  rw [hY] at h4
  rw [hsplit]
  norm_num at h4
  linear_combination -h4

/-- **R04-08**: the residue of P_{m,3} is APN (no hypothesis). -/
theorem resAPN3 (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m)
    (h3 : Nat.Coprime 3 m) : GRS.ResAPN (Fnat3 K m) := by
  intro c hc b
  have h3K : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by have h2 : (2 : K) = 0 := two_K; linear_combination h2
    rw [this]; exact one_ne_zero
  exact resAPN_of_cube _ (Y3 m) (Y3_add m) (Y3_inj m (by omega) hcard h3)
    (p3_cube m (by omega) hcard) h3K c hc b

/-- **R04-08**: the residue of P_{m,r} (r ≥ 5) is APN (no hypothesis). -/
theorem resAPN5 (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hcard : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (hodd : Odd r) : GRS.ResAPN (F5 K m r) := by
  intro c hc b
  have h3K : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by have h2 : (2 : K) = 0 := two_K; linear_combination h2
    rw [this]; exact one_ne_zero
  exact resAPN_of_cube _ (Y5 m r) (Y5_add m r) (Y5_inj m r (by omega) (by omega) hcard hcop hodd)
    (p5_cube m r (by omega) (by omega) hcard) h3K c hc b

end family

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- **Theorem A (r = 3), all unit directions, no APN hypothesis.** -/
theorem fam3_units' (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ) (hm5 : 5 ≤ m)
    (hodd : Odd m) (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) (α β : R) (hα : S.π α ≠ 0) :
    delta (Fsh3 R m) α β ≤ 2 * Fintype.card K ∧ (S.π α ≠ 1 → delta (Fsh3 R m) α β ≤ 2) := by
  haveI := S.charP2
  exact S.fam3_units hcard m hm5 hodd hm h3 (resAPN3 m hm5 hm h3) α β hα

/-- **Theorem A (r ≥ 5), all unit directions, no APN hypothesis.** -/
theorem fam5_units' (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (α β : R) (hα : S.π α ≠ 0) :
    delta (Fsh5 R m r) α β ≤ 2 * Fintype.card K ∧ (S.π α ≠ 1 → delta (Fsh5 R m r) α β ≤ 2) := by
  haveI := S.charP2
  exact S.fam5_units hcard m r hm5 hr5 hrm hodd hmodd hm hcop (resAPN5 m r hm5 hr5 hm hcop hodd) α β hα

end GRS

end APN2

#print axioms APN2.resAPN3
#print axioms APN2.resAPN5
#print axioms APN2.GRS.fam3_units'
#print axioms APN2.GRS.fam5_units'
