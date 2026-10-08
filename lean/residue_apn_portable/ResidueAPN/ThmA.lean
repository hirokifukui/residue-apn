import ResidueAPN.Family

/-!
# Theorem 3.1 (A) of paper_R5 — the map side

`F` is a finite field of characteristic two with `card F = 2 ^ m`, `m` odd, `m ≥ 5`;
`r` is admissible: odd, `3 ≤ r < m`, `gcd(r, m) = 1`. `P = polP F m r` (the image of the
`𝔽₂`-polynomial, `map_polP`).

* `eval_polP` (Theorem 3.1(2), first half, as maps): `P(x) = ((T_r x)^3)^(2^(m-2))`.
* `degree_polP_lt`: `deg P < q`, so `P` is the reduced representative (`rep_eval_polP`).
* `bijective_evalP`, `isAPN_evalP` (Theorem 3.1(2)).
* `evalD_ne_zero`, `evalD_fibre` (Theorem 3.1(3)): `P' = D` has no zero; its fibres are `{x, x+1}`.
* `isOptimalAPNPerm_P`: `x ↦ P(x)` is an optimal APN permutation (Definition 2.1).
-/

namespace ResidueAPN

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

section Eval

/-- `T_r(x)^(2^(m-2)) = V(x) + Y(x) + Z(x)` on `F` (`x^(2^m) = x`). -/
theorem eval_polT_frob {m r : ℕ} (hm : 2 ≤ m) (hr : 2 ≤ r) {x : F} (hx : x ^ (2 ^ m) = x) :
    (polT F r).eval x ^ (2 ^ (m - 2))
      = (polV F r).eval x + (polY F m).eval x + (polZ F m).eval x := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  simp only [polT, polV, polY, polZ, eval_finsetSum, eval_pow, eval_X, Nat.add_sub_cancel]
  rw [frob_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  have key : ∀ i, (x ^ 2 ^ i) ^ 2 ^ (m - 2) = x ^ 2 ^ (i + (m - 2)) := fun i => by
    rw [← pow_mul, ← pow_add]
  simp only [key]
  have h1 : ∀ i, x ^ 2 ^ (i + 1 + 1 + (m - 2)) = x ^ 2 ^ i := fun i => by
    rw [show i + 1 + 1 + (m - 2) = m + i by omega, pow_add, pow_mul, hx]
  simp only [h1]
  rw [show 0 + 1 + (m - 2) = m - 1 by omega, show 0 + (m - 2) = m - 2 by omega]
  ring

/-- `V(x)^2 = V(x) + W(x) + x` in characteristic two (`r ≥ 2`). -/
theorem eval_polV_sq {r : ℕ} (hr : 2 ≤ r) (x : F) :
    (polV F r).eval x ^ 2 = (polV F r).eval x + (polW F r).eval x + x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [polV, polW, eval_finsetSum, eval_pow, eval_X]
  have hs := Finset.sum_range_succ' (fun i => x ^ 2 ^ i) (r - 2)
  rw [Finset.sum_range_succ] at hs
  rw [show (∑ i ∈ range (r - 2), x ^ 2 ^ i) ^ 2 = ∑ i ∈ range (r - 2), x ^ 2 ^ (i + 1) by
    rw [show (2 : ℕ) = 2 ^ 1 by norm_num, frob_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← pow_mul, ← pow_succ]]
  simp only [pow_zero, pow_one] at hs
  linear_combination (-1 : F) * hs + (-x) * h2

/-- **Theorem 3.1(2), as maps.** `P(x) = ((T_r x)^3)^(2^(m-2))`. -/
theorem eval_polP {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm : 2 ≤ m) (hr : 2 ≤ r) (x : F) :
    (polP F m r).eval x = ((polT F r).eval x ^ 3) ^ (2 ^ (m - 2)) := by
  have hx := pow_card_two_pow hcard x
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [← pow_mul, mul_comm, pow_mul, eval_polT_frob hm hr hx]
  have hV2 := eval_polV_sq (F := F) hr x
  have hY2 : (polY F m).eval x ^ 2 = (polZ F m).eval x := by
    simp only [polY, polZ, eval_pow, eval_X]
    rw [← pow_mul, ← pow_succ]; congr 2; omega
  have hZ2 : (polZ F m).eval x ^ 2 = x := by
    simp only [polZ, eval_pow, eval_X]
    rw [← pow_mul, ← pow_succ, show m - 1 + 1 = m by omega, hx]
  simp only [polP, eval_add, eval_mul]
  set v := (polV F r).eval x
  set w := (polW F r).eval x
  set y := (polY F m).eval x
  set z := (polZ F m).eval x
  linear_combination (-v - 3*y - 3*z - 1) * hV2 + (-3*v - y - 3*z) * hY2
    + (-3*v - 3*y - z - 3) * hZ2
    + (-2*v*x - 3*v*y*z - v*y - 3*v*z - w*y - w*z - 3*x*y - 2*x*z - 2*x) * h2

end Eval

section Degree

theorem natDegree_polV_le {m r : ℕ} (hrm : r ≤ m) : (polV F r).natDegree ≤ 2 ^ (m - 2) := by
  unfold polV
  refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
  rw [natDegree_X_pow]
  exact Nat.pow_le_pow_right (by norm_num) (by simp at hi; omega)

/-- `deg P ≤ 3 · 2^(m-2) < 2^m`. -/
theorem natDegree_polP_le {m r : ℕ} (hrm : r ≤ m) (hm : 2 ≤ m) :
    (polP F m r).natDegree ≤ 3 * 2 ^ (m - 2) := by
  have hV := natDegree_polV_le (F := F) hrm
  have hW : (polW F r).natDegree ≤ 2 ^ (m - 2) := by
    rw [polW, natDegree_X_pow]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hY : (polY F m).natDegree ≤ 2 ^ (m - 2) := by rw [polY, natDegree_X_pow]
  have hZ : (polZ F m).natDegree ≤ 2 * 2 ^ (m - 2) := by
    rw [polZ, natDegree_X_pow, ← pow_succ']; exact le_of_eq (by congr 1; omega)
  unfold polP
  have hmul : ∀ {p q : F[X]} {a b : ℕ}, p.natDegree ≤ a → q.natDegree ≤ b →
      (p * q).natDegree ≤ a + b := fun {p q _ _} hp hq =>
    (natDegree_mul_le (p := p) (q := q)).trans (Nat.add_le_add hp hq)
  have e := Nat.zero_le (2 ^ (m - 2))
  have t1 := hmul hW hV
  have t2 := hmul hW hY
  have t3 := hmul hW hZ
  have t4 := hmul hY hV
  have t5 := hmul hY hZ
  have hadd : ∀ {p q : F[X]} {n : ℕ}, p.natDegree ≤ n → q.natDegree ≤ n → (p + q).natDegree ≤ n :=
    fun {p q _} h1 h2 => (natDegree_add_le p q).trans (max_le h1 h2)
  exact hadd (hadd (hadd (hadd (hadd (hadd (by omega) (by omega)) (by omega)) (by omega))
    (by omega)) (by omega)) (by omega)

theorem degree_polP_lt {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hrm : r ≤ m) (hm : 2 ≤ m) :
    (polP F m r).degree < Fintype.card F := by
  refine degree_le_natDegree.trans_lt ?_
  rw [hcard]
  have h := natDegree_polP_le (F := F) hrm hm
  have hc : 0 < 2 ^ (m - 2) := by positivity
  have h4 : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  exact_mod_cast (show (polP F m r).natDegree < 2 ^ m by omega)

/-- `P` is the reduced representative of the map `x ↦ P(x)`. -/
theorem rep_eval_polP {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hrm : r ≤ m) (hm : 2 ≤ m) :
    rep (fun x : F => (polP F m r).eval x) = polP F m r :=
  (rep_unique (degree_polP_lt hcard hrm hm) (fun _ => rfl)).symm

end Degree

section Maps

/-- Frobenius powers are injective. -/
theorem frob_injective (k : ℕ) : Function.Injective (fun x : F => x ^ (2 ^ k)) := by
  intro a b h
  have : (a + b) ^ (2 ^ k) = 0 := by
    simp only at h; rw [frob_add, h, CharTwo.add_self_eq_zero]
  exact CharTwo.add_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp this)

/-- `T_r` is additive. -/
theorem evalT_add (r : ℕ) (x y : F) :
    (polT F r).eval (x + y) = (polT F r).eval x + (polT F r).eval y := by
  simp only [polT, eval_finsetSum, eval_pow, eval_X, frob_add, Finset.sum_add_distrib]

/-- `T_r(x)^2 + T_r(x) = x^(2^r) + x`. -/
theorem evalT_sq_add (r : ℕ) (x : F) :
    (polT F r).eval x ^ 2 + (polT F r).eval x = x ^ (2 ^ r) + x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [polT, eval_finsetSum, eval_pow, eval_X]
  have hs := Finset.sum_range_succ' (fun i => x ^ 2 ^ i) r
  rw [Finset.sum_range_succ] at hs
  rw [show (∑ i ∈ range r, x ^ 2 ^ i) ^ 2 = ∑ i ∈ range r, x ^ 2 ^ (i + 1) by
    rw [show (2 : ℕ) = 2 ^ 1 by norm_num, frob_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← pow_mul, ← pow_succ]]
  simp only [pow_zero, pow_one] at hs
  linear_combination (-1 : F) * hs + (∑ i ∈ range r, x ^ 2 ^ i - x) * h2

/-- `T_r` is injective (admissible `r`: odd, `gcd(r, m) = 1`). -/
theorem evalT_injective {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hrodd : Odd r)
    (hcop : Nat.Coprime r m) : Function.Injective (fun x : F => (polT F r).eval x) := by
  have hker : ∀ x : F, (polT F r).eval x = 0 → x = 0 := by
    intro x hx
    have h := evalT_sq_add (F := F) r x
    rw [hx, zero_pow two_ne_zero, add_zero, eq_comm] at h
    have hfix : x ^ (2 ^ r) = x := CharTwo.add_eq_zero.mp h
    rcases eq_zero_or_one_of_fixed hcop hfix (pow_card_two_pow hcard x) with h0 | h1
    · exact h0
    · exfalso
      rw [h1] at hx
      simp only [polT, eval_finsetSum, eval_pow, eval_X, one_pow, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one] at hx
      rw [natCast_of_odd hrodd] at hx
      exact one_ne_zero hx
  intro x y hxy
  simp only at hxy
  have : (polT F r).eval (x + y) = 0 := by rw [evalT_add, hxy, CharTwo.add_self_eq_zero]
  exact CharTwo.add_eq_zero.mp (hker _ this)

/-- `gcd(3, 2^m - 1) = 1` for odd `m`. -/
theorem coprime_three_two_pow_sub_one {m : ℕ} (hm : Odd m) : Nat.Coprime 3 (2 ^ m - 1) := by
  obtain ⟨t, rfl⟩ := hm
  have h4 : 4 ^ t % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h2 : 2 ^ (2 * t + 1) = 2 * 4 ^ t := by rw [pow_succ, pow_mul]; norm_num; ring
  have hpos : 1 ≤ 4 ^ t := Nat.one_le_pow _ _ (by norm_num)
  have hmod : (2 ^ (2 * t + 1) - 1) % 3 = 1 := by rw [h2]; omega
  rw [Nat.Coprime, Nat.gcd_rec, hmod]
  norm_num

/-- The cube map is injective on `F` (`m` odd). -/
theorem cube_injective {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm : Odd m) :
    Function.Injective (fun x : F => x ^ 3) := by
  intro x y hxy
  simp only at hxy
  by_cases hy : y = 0
  · subst hy; rw [zero_pow (by norm_num)] at hxy; exact pow_eq_zero_iff (by norm_num) |>.mp hxy
  · set z := x * y⁻¹
    have hz3 : z ^ 3 = 1 := by
      rw [mul_pow, hxy, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hy)]
    have hz0 : z ≠ 0 := by
      intro h; rw [h, zero_pow (by norm_num)] at hz3; exact zero_ne_one hz3
    have hzq : z ^ (2 ^ m - 1) = 1 := by
      rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one z hz0
    have hg : z ^ (Nat.gcd 3 (2 ^ m - 1)) = 1 := pow_gcd_eq_one.mpr ⟨hz3, hzq⟩
    rw [coprime_three_two_pow_sub_one hm, pow_one] at hg
    calc x = z * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
      _ = y := by rw [hg, one_mul]

/-- The map `x ↦ P(x)` factors as `σ^(m-2) ∘ X^3 ∘ T_r`. -/
theorem evalP_eq_comp {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    (fun x : F => (polP F m r).eval x)
      = (fun u : F => u ^ (2 ^ (m - 2))) ∘ (fun u : F => u ^ 3) ∘ (fun x : F => (polT F r).eval x) := by
  funext x; exact eval_polP hcard hm hr x

/-- **Theorem 3.1(2): bijective.** -/
theorem bijective_evalP {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hmodd : Odd m)
    (hr : 3 ≤ r) (hrodd : Odd r) (hcop : Nat.Coprime r m) :
    Function.Bijective (fun x : F => (polP F m r).eval x) := by
  rw [← Finite.injective_iff_bijective, evalP_eq_comp hcard (by omega) (by omega)]
  exact (frob_injective _).comp ((cube_injective hcard hmodd).comp (evalT_injective hcard hrodd hcop))

end Maps

section APN

/-- APN is preserved by `N ∘ G ∘ A` with `N`, `A` additive and injective. -/
theorem isAPN_comp {G N A : F → F} (hG : IsAPN G)
    (hNadd : ∀ x y, N (x + y) = N x + N y) (hNinj : Function.Injective N)
    (hAadd : ∀ x y, A (x + y) = A x + A y) (hAinj : Function.Injective A) :
    IsAPN (N ∘ G ∘ A) := by
  intro a ha b
  have hNsurj := Finite.injective_iff_surjective.mp hNinj
  obtain ⟨b', rfl⟩ := hNsurj b
  have hA0 : A 0 = 0 := by
    have := hAadd 0 0; rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  have hAa : A a ≠ 0 := fun h => ha (hAinj (h.trans hA0.symm))
  refine le_trans (Finset.card_le_card_of_injOn A ?_ hAinj.injOn) (hG (A a) hAa b')
  intro x hx
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
  simp only [deriv, Function.comp, hAadd] at hx ⊢
  rw [← hNadd] at hx
  exact hNinj hx

/-- The cube map is APN in characteristic two. -/
theorem isAPN_cube : IsAPN (fun x : F => x ^ 3) := by
  intro a ha b
  classical
  let q : F[X] := C a * X ^ 2 + C (a ^ 2) * X + C (a ^ 3 + b)
  have hq : q.natDegree = 2 := natDegree_quadratic ha
  have hq0 : q ≠ 0 := by intro h; rw [h, natDegree_zero] at hq; exact two_ne_zero hq.symm
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsub : (Finset.univ.filter (fun x : F => deriv (fun x : F => x ^ 3) a x = b))
      ⊆ q.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, deriv] at hx
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot.def]
    simp only [q, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination hx + (-x ^ 3 - x ^ 2 * a - x * a ^ 2 + b) * h2
  calc _ ≤ q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := card_roots' q
    _ = 2 := hq

/-- **Theorem 3.1(2): APN.** -/
theorem isAPN_evalP {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hmodd : Odd m)
    (hr : 3 ≤ r) (hrodd : Odd r) (hcop : Nat.Coprime r m) :
    IsAPN (fun x : F => (polP F m r).eval x) := by
  have h := evalP_eq_comp (F := F) (m := m) (r := r) hcard (by omega) (by omega)
  rw [h, ← Function.comp_assoc]
  have := isAPN_comp (G := fun u : F => u ^ 3) (N := fun u : F => u ^ (2 ^ (m - 2)))
    (A := fun x : F => (polT F r).eval x) isAPN_cube (fun x y => frob_add _ x y)
    (frob_injective _) (evalT_add r) (evalT_injective hcard hrodd hcop)
  simpa [Function.comp_def] using this

end APN

section Derivative

/-- `D(x) = 1 + (x^(2^r) + x)^(2^(m-2))` on `F`. -/
theorem evalD_eq {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm : 2 ≤ m) (hr : 2 ≤ r) (x : F) :
    (polD F m r).eval x = 1 + (x ^ (2 ^ r) + x) ^ (2 ^ (m - 2)) := by
  have hx := pow_card_two_pow hcard x
  simp only [polD, polW, polY, eval_add, eval_one, eval_pow, eval_X]
  rw [frob_add, ← pow_mul, ← pow_add, show r + (m - 2) = m + (r - 2) by omega, pow_add, pow_mul, hx]
  ring

/-- **Theorem 3.1(3): `P' = D` has no zero on `F`.** -/
theorem evalD_ne_zero {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hmodd : Odd m)
    (hr : 3 ≤ r) (x : F) : (polD F m r).eval x ≠ 0 := by
  rw [evalD_eq hcard (by omega) (by omega)]
  intro h
  have h1 : (x ^ (2 ^ r) + x) ^ (2 ^ (m - 2)) = (1 : F) ^ (2 ^ (m - 2)) := by
    rw [one_pow]; linear_combination h + (-1 : F) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have h2 := frob_injective (F := F) (m - 2) h1
  apply no_shift_fixed (pow_card_two_pow hcard x) hmodd (r := r)
  linear_combination h2 + (-x) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- **Theorem 3.1(3): the fibres of `P' = D` are `{x, x + 1}`.** -/
theorem evalD_eq_iff {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m)
    (hr : 3 ≤ r) (hcop : Nat.Coprime r m) (x y : F) :
    (polD F m r).eval y = (polD F m r).eval x ↔ y = x ∨ y = x + 1 := by
  rw [evalD_eq hcard (by omega) (by omega), evalD_eq hcard (by omega) (by omega)]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have hAB : (y ^ 2 ^ r + y) ^ 2 ^ (m - 2) = (x ^ 2 ^ r + x) ^ 2 ^ (m - 2) := add_left_cancel h
    have h' : (y + x) ^ (2 ^ r) + (y + x) = 0 := by
      have e : ((y + x) ^ (2 ^ r) + (y + x)) ^ (2 ^ (m - 2)) = 0 := by
        calc ((y + x) ^ (2 ^ r) + (y + x)) ^ (2 ^ (m - 2))
            = ((y ^ 2 ^ r + y) + (x ^ 2 ^ r + x)) ^ (2 ^ (m - 2)) := by rw [frob_add r y x]; ring_nf
          _ = (y ^ 2 ^ r + y) ^ 2 ^ (m - 2) + (x ^ 2 ^ r + x) ^ 2 ^ (m - 2) := frob_add _ _ _
          _ = 0 := by rw [hAB, CharTwo.add_self_eq_zero]
      exact (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp e
    have hfix : (y + x) ^ (2 ^ r) = y + x := CharTwo.add_eq_zero.mp h'
    rcases eq_zero_or_one_of_fixed hcop hfix (pow_card_two_pow hcard _) with h0 | h1
    · left; exact CharTwo.add_eq_zero.mp h0
    · right; linear_combination h1 + (-x) * h2
  · rintro (rfl | rfl)
    · rfl
    · rw [frob_add r x 1, one_pow]
      have e : x ^ 2 ^ r + 1 + (x + 1) = x ^ 2 ^ r + x := by linear_combination h2
      rw [e]

theorem evalD_fibre_card {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m)
    (hr : 3 ≤ r) (hcop : Nat.Coprime r m) (x : F) :
    (Finset.univ.filter (fun y : F => (polD F m r).eval y = (polD F m r).eval x)).card = 2 := by
  have : Finset.univ.filter (fun y : F => (polD F m r).eval y = (polD F m r).eval x) = {x, x + 1} := by
    ext y; simp [evalD_eq_iff hcard hm5 hr hcop x y]
  rw [this, Finset.card_pair]
  intro h
  have : (1 : F) = 0 := by linear_combination -h
  exact one_ne_zero this

/-- **Theorem 3.1(2)+(3).** For admissible `r`, `x ↦ P_{m,r}(x)` is an optimal APN permutation
of `F`, and its reduced representative is `P_{m,r}` itself. -/
theorem isOptimalAPNPerm_P {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m)
    (hmodd : Odd m) (hr : 3 ≤ r) (hrm : r < m) (hrodd : Odd r) (hcop : Nat.Coprime r m) :
    IsOptimalAPNPerm (fun x : F => (polP F m r).eval x) := by
  refine ⟨isAPN_evalP hcard hm5 hmodd hr hrodd hcop, bijective_evalP hcard hm5 hmodd hr hrodd hcop, ?_⟩
  rw [rep_eval_polP hcard hrm.le (by omega), IsDerivOptimal, derivative_polP hr (by omega)]
  exact ⟨evalD_ne_zero hcard hm5 hmodd hr, evalD_fibre_card hcard hm5 hr hcop⟩

end Derivative

end ResidueAPN
