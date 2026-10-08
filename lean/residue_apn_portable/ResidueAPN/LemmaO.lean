import ResidueAPN.ThmAImage

/-!
# Lemma 2.2 of the paper — the derivative-optimality criterion for quadratic polynomials over `𝔽_2`

For `κ ∈ 𝔽_2[t]` let `κ(σ)` be the `𝔽_2`-linear map `x ↦ ∑ κ_i x^(2^i)` of `F = 𝔽_{2^m}` (`linMap κ`).
For a quadratic `p` with coefficients in `𝔽_2`, `p' = ε + κ(σ)` (display (1) of the paper; `derivative_quadratic`).

The proof here does not use a normal basis (the paper's proof does). It uses:
* `linMap_mul`: `(φψ)(σ) = φ(σ) ∘ ψ(σ)`; `linMap_X_pow_sub_one`: `(t^m - 1)(σ) = 0`;
* `card_ker_le`: `#ker φ(σ) ≤ 2^(deg φ)` (roots of a nonzero polynomial of degree `2^(deg φ)`);
* `card_ker_comp_le`: `#ker (A ∘ B) ≤ #ker A · #ker B`;
* hence `#ker φ(σ) = 2^(deg φ)` for `φ ∣ t^m - 1` (`card_ker_of_dvd`), and `ker κ(σ) = ker g(σ)` for
  `g = gcd(κ, t^m - 1)` (Bézout);
* the image of `(t+1)(σ) = x^2 + x` lies in `ker Tr`, and `Tr 1 = 1` for odd `m`.
-/

namespace ResidueAPN

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The cast `𝔽_2 → F`. -/
noncomputable abbrev c2 (F : Type*) [Field F] [CharP F 2] : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

/-- `κ(σ)`: the `𝔽_2`-linear map `x ↦ ∑_i κ_i x^(2^i)`. -/
noncomputable def linMap (κ : (ZMod 2)[X]) (x : F) : F :=
  κ.sum (fun i c => c2 F c * x ^ (2 ^ i))

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · left; rfl
  · right; rfl

theorem c2_pow_two_pow (c : ZMod 2) (k : ℕ) : (c2 F c) ^ (2 ^ k) = c2 F c := by
  rcases zmod2_cases c with rfl | rfl
  · rw [map_zero, zero_pow (by positivity)]
  · rw [map_one, one_pow]

theorem linMap_add_poly (φ ψ : (ZMod 2)[X]) (x : F) :
    linMap (φ + ψ) x = linMap φ x + linMap ψ x := by
  unfold linMap
  exact sum_add_index φ ψ _ (fun i => by simp) (fun i a b => by rw [map_add, add_mul])

theorem linMap_monomial (i : ℕ) (c : ZMod 2) (x : F) :
    linMap (monomial i c) x = c2 F c * x ^ (2 ^ i) := by
  unfold linMap
  exact sum_monomial_index c (fun i c => c2 F c * x ^ (2 ^ i)) (by simp)

theorem linMap_zero_poly (x : F) : linMap (0 : (ZMod 2)[X]) x = 0 := by
  simp [linMap]

theorem linMap_add (κ : (ZMod 2)[X]) (x y : F) :
    linMap κ (x + y) = linMap κ x + linMap κ y := by
  induction κ using Polynomial.induction_on' with
  | add φ ψ hφ hψ => rw [linMap_add_poly, linMap_add_poly, linMap_add_poly, hφ, hψ]; ring
  | monomial i c => rw [linMap_monomial, linMap_monomial, linMap_monomial, frob_add, mul_add]

theorem linMap_zero (κ : (ZMod 2)[X]) : linMap κ (0 : F) = 0 := by
  have h := linMap_add κ (0 : F) 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

theorem linMap_pow_two_pow (κ : (ZMod 2)[X]) (k : ℕ) (x : F) :
    (linMap κ x) ^ (2 ^ k) = linMap (X ^ k * κ) x := by
  induction κ using Polynomial.induction_on' with
  | add φ ψ hφ hψ => rw [linMap_add_poly, frob_add, hφ, hψ, mul_add, linMap_add_poly]
  | monomial i c =>
    rw [linMap_monomial, X_pow_mul_monomial, linMap_monomial, mul_pow, c2_pow_two_pow, ← pow_mul,
      ← pow_add]

theorem linMap_C_mul (a : ZMod 2) (κ : (ZMod 2)[X]) (x : F) :
    linMap (C a * κ) x = c2 F a * linMap κ x := by
  induction κ using Polynomial.induction_on' with
  | add φ ψ hφ hψ => rw [mul_add, linMap_add_poly, linMap_add_poly, hφ, hψ, mul_add]
  | monomial i c => rw [C_mul_monomial, linMap_monomial, linMap_monomial, map_mul, mul_assoc]

/-- `(φψ)(σ) = φ(σ) ∘ ψ(σ)`. -/
theorem linMap_mul (φ ψ : (ZMod 2)[X]) (x : F) :
    linMap (φ * ψ) x = linMap φ (linMap ψ x) := by
  induction φ using Polynomial.induction_on' with
  | add φ₁ φ₂ h₁ h₂ => rw [add_mul, linMap_add_poly, linMap_add_poly, h₁, h₂]
  | monomial i c =>
    rw [linMap_monomial, ← C_mul_X_pow_eq_monomial, mul_assoc, linMap_C_mul, ← linMap_pow_two_pow]

theorem linMap_X (x : F) : linMap (X : (ZMod 2)[X]) x = x ^ 2 := by
  rw [← monomial_one_one_eq_X, linMap_monomial]; simp

theorem linMap_one (x : F) : linMap (1 : (ZMod 2)[X]) x = x := by
  rw [← monomial_zero_one, linMap_monomial]; simp

theorem linMap_X_pow_sub_one {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (x : F) :
    linMap ((X : (ZMod 2)[X]) ^ m - 1) x = 0 := by
  rw [sub_eq_add_neg, linMap_add_poly, ← monomial_one_right_eq_X_pow, linMap_monomial, ← C_1,
    ← C_neg, ← monomial_zero_left, linMap_monomial, pow_card_two_pow hcard]
  simp only [map_one, one_mul, map_neg, pow_zero, pow_one]
  rw [neg_one_mul, ← sub_eq_add_neg, sub_self]

/-- The kernel of `κ(σ)`. -/
noncomputable def kerL (κ : (ZMod 2)[X]) : Finset F := univ.filter (fun x : F => linMap κ x = 0)

/-- The polynomial `∑ κ_i X^(2^i)` whose roots are the kernel of `κ(σ)`. -/
noncomputable def linPoly (F : Type*) [Field F] [CharP F 2] (κ : (ZMod 2)[X]) : F[X] :=
  κ.sum (fun i c => C (c2 F c) * X ^ (2 ^ i))

theorem eval_linPoly (κ : (ZMod 2)[X]) (x : F) : (linPoly F κ).eval x = linMap κ x := by
  simp only [linPoly, linMap, Polynomial.sum, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem coeff_linPoly_two_pow (κ : (ZMod 2)[X]) (d : ℕ) :
    (linPoly F κ).coeff (2 ^ d) = c2 F (κ.coeff d) := by
  simp only [linPoly, Polynomial.sum, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  by_cases hd : d ∈ κ.support
  · rw [sum_eq_single d]
    · simp
    · intro i _ hi
      have : 2 ^ d ≠ 2 ^ i := fun h => hi (Nat.pow_right_injective (le_refl 2) h).symm
      simp [this]
    · intro h; exact absurd hd h
  · rw [notMem_support_iff.mp hd, map_zero]
    refine sum_eq_zero (fun i hi => ?_)
    have : 2 ^ d ≠ 2 ^ i := fun h => by
      rw [Nat.pow_right_injective (le_refl 2) h] at hd; exact hd hi
    simp [this]

theorem natDegree_linPoly_le (κ : (ZMod 2)[X]) : (linPoly F κ).natDegree ≤ 2 ^ κ.natDegree := by
  unfold linPoly Polynomial.sum
  refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Nat.pow_le_pow_right (by norm_num) (le_natDegree_of_mem_supp i hi)

theorem linPoly_ne_zero {κ : (ZMod 2)[X]} (hκ : κ ≠ 0) : linPoly F κ ≠ 0 := by
  intro h
  have hl : κ.leadingCoeff = 1 :=
    (zmod2_cases _).resolve_left (leadingCoeff_ne_zero.mpr hκ)
  have := coeff_linPoly_two_pow (F := F) κ κ.natDegree
  rw [h, coeff_zero, ← leadingCoeff, hl, map_one] at this
  exact zero_ne_one this

/-- `#ker κ(σ) ≤ 2^(deg κ)`. -/
theorem card_kerL_le {κ : (ZMod 2)[X]} (hκ : κ ≠ 0) : (kerL (F := F) κ).card ≤ 2 ^ κ.natDegree := by
  have hT0 := linPoly_ne_zero (F := F) hκ
  have hsub : kerL (F := F) κ ⊆ (linPoly F κ).roots.toFinset := by
    intro y hy
    simp only [kerL, mem_filter, mem_univ, true_and] at hy
    rw [Multiset.mem_toFinset, mem_roots hT0, IsRoot.def, eval_linPoly]
    exact hy
  calc _ ≤ (linPoly F κ).roots.toFinset.card := card_le_card hsub
    _ ≤ Multiset.card (linPoly F κ).roots := Multiset.toFinset_card_le _
    _ ≤ (linPoly F κ).natDegree := card_roots' _
    _ ≤ 2 ^ κ.natDegree := natDegree_linPoly_le κ

/-- `#ker (φψ)(σ) ≤ #ker φ(σ) · #ker ψ(σ)`. -/
theorem card_kerL_mul_le (φ ψ : (ZMod 2)[X]) :
    (kerL (F := F) (φ * ψ)).card ≤ (kerL (F := F) ψ).card * (kerL (F := F) φ).card := by
  refine (card_le_mul_card_image (f := fun x : F => linMap ψ x) (kerL (F := F) (φ * ψ))
    (kerL (F := F) ψ).card ?_).trans ?_
  · intro y _
    by_cases hne : ((kerL (F := F) (φ * ψ)).filter (fun x => linMap ψ x = y)).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      simp only [mem_filter] at hx₀
      refine card_le_card_of_injOn (fun x => x - x₀) (fun x hx => ?_) (fun a _ b _ h => ?_)
      · rw [Finset.mem_coe, mem_filter] at hx
        simp only [kerL, mem_filter, mem_univ, true_and] at hx
        rw [Finset.mem_coe]; simp only [kerL, mem_filter, mem_univ, true_and]
        have h1 := linMap_add ψ (x - x₀) x₀
        rw [sub_add_cancel, hx.2, hx₀.2] at h1
        exact add_eq_right.mp h1.symm
      · simpa using h
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]; exact Nat.zero_le _
  · refine Nat.mul_le_mul_left _ (card_le_card (fun y hy => ?_))
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    simp only [kerL, mem_filter, mem_univ, true_and] at hx ⊢
    rwa [linMap_mul] at hx

/-- For `φ ∣ t^m - 1`, `#ker φ(σ) = 2^(deg φ)`. -/
theorem card_kerL_of_dvd {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm : 1 ≤ m)
    {φ : (ZMod 2)[X]} (hφ : φ ∣ X ^ m - 1) : (kerL (F := F) φ).card = 2 ^ φ.natDegree := by
  obtain ⟨ψ, hψ⟩ := hφ
  have hne : (X : (ZMod 2)[X]) ^ m - 1 ≠ 0 := X_pow_sub_C_ne_zero (by omega) 1
  have hφ0 : φ ≠ 0 := by rintro rfl; rw [zero_mul] at hψ; exact hne hψ
  have hψ0 : ψ ≠ 0 := by rintro rfl; rw [mul_zero] at hψ; exact hne hψ
  have hdeg : φ.natDegree + ψ.natDegree = m := by
    rw [← natDegree_mul hφ0 hψ0, ← hψ, ← C_1, natDegree_X_pow_sub_C]
  have hall : (kerL (F := F) (φ * ψ)).card = 2 ^ m := by
    rw [← hψ, ← hcard]
    rw [show kerL (F := F) ((X : (ZMod 2)[X]) ^ m - 1) = univ from
      filter_true_of_mem (fun x _ => linMap_X_pow_sub_one hcard x), card_univ]
  have h1 := card_kerL_mul_le (F := F) φ ψ
  have h2 := card_kerL_le (F := F) hψ0
  have h3 := card_kerL_le (F := F) hφ0
  rw [hall] at h1
  have hpos : 0 < 2 ^ ψ.natDegree := by positivity
  have : 2 ^ φ.natDegree * 2 ^ ψ.natDegree ≤ (kerL (F := F) φ).card * 2 ^ ψ.natDegree := by
    rw [← pow_add, hdeg]
    calc 2 ^ m ≤ _ := h1
      _ = (kerL (F := F) φ).card * (kerL (F := F) ψ).card := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  exact le_antisymm h3 (Nat.le_of_mul_le_mul_right this hpos)

/-- `ker κ(σ) = ker g(σ)` for `g = gcd(κ, t^m - 1)`. -/
theorem kerL_gcd {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (κ : (ZMod 2)[X]) :
    kerL (F := F) κ = kerL (F := F) (EuclideanDomain.gcd κ (X ^ m - 1)) := by
  ext x
  simp only [kerL, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    rw [EuclideanDomain.gcd_eq_gcd_ab, linMap_add_poly, mul_comm κ, linMap_mul, h, linMap_zero,
      mul_comm (X ^ m - 1), linMap_mul, linMap_X_pow_sub_one hcard, linMap_zero, add_zero]
  · intro h
    obtain ⟨w, hw⟩ := EuclideanDomain.gcd_dvd_left κ (X ^ m - 1)
    conv_lhs => rw [hw, mul_comm, linMap_mul, h, linMap_zero]

theorem eq_X_add_one_of_dvd {m : ℕ} (hm : 1 ≤ m) {g : (ZMod 2)[X]} (hg : g ∣ X ^ m - 1)
    (h1 : g.natDegree = 1) : g = X + 1 := by
  have hform := eq_X_add_C_of_natDegree_le_one (show g.natDegree ≤ 1 by omega)
  have ha : g.coeff 1 ≠ 0 := by
    have hg0 : g ≠ 0 := by rintro rfl; rw [natDegree_zero] at h1; exact absurd h1 (by norm_num)
    have := leadingCoeff_ne_zero.mpr hg0
    rwa [leadingCoeff, h1] at this
  have ha1 : g.coeff 1 = 1 := (zmod2_cases _).resolve_left ha
  have hb : g.coeff 0 ≠ 0 := by
    intro hb
    rw [hb, ha1, C_0, add_zero, C_1, one_mul] at hform
    rw [hform] at hg
    have := eval_eq_zero_of_dvd_of_eval_eq_zero hg (by rw [eval_X] : (X : (ZMod 2)[X]).eval 0 = 0)
    rw [eval_sub, eval_pow, eval_X, eval_one, zero_pow (by omega : m ≠ 0), zero_sub, neg_eq_zero] at this
    exact one_ne_zero this
  have hb1 : g.coeff 0 = 1 := (zmod2_cases _).resolve_left hb
  rw [hform, ha1, hb1, C_1, one_mul]

theorem absTr_one_of_odd {m : ℕ} (hm : Odd m) : absTr m (1 : F) = 1 := by
  simp only [absTr, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  exact natCast_of_odd hm

theorem absTr_sq_add {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (z : F) : absTr m (z ^ 2 + z) = 0 := by
  rw [absTr_add, absTr_sq hcard, CharTwo.add_self_eq_zero]

/-- **Lemma 2.2, core form.** For `ε ∈ 𝔽_2` and `κ ∈ 𝔽_2[t]`, the map `x ↦ ε + κ(σ)(x)` has no zero and
two-element fibres iff `ε = 1` and `gcd(κ, t^m - 1) = t + 1`. -/
theorem lemma_2_2_core {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (hmodd : Odd m)
    (ε : ZMod 2) (κ : (ZMod 2)[X]) :
    ((∀ x : F, c2 F ε + linMap κ x ≠ 0) ∧
      ∀ x : F, (univ.filter (fun y : F => c2 F ε + linMap κ y = c2 F ε + linMap κ x)).card = 2)
    ↔ ε = 1 ∧ EuclideanDomain.gcd κ (X ^ m - 1) = X + 1 := by
  have hm : 1 ≤ m := hmodd.pos
  have hg := EuclideanDomain.gcd_dvd_right κ ((X : (ZMod 2)[X]) ^ m - 1)
  have hfib : ∀ x : F, (univ.filter (fun y : F => c2 F ε + linMap κ y = c2 F ε + linMap κ x)).card
      = (kerL (F := F) κ).card := by
    intro x
    refine card_bij (fun y _ => y - x) (fun y hy => ?_) (fun a _ b _ h => by simpa using h)
      (fun z hz => ⟨z + x, ?_, by ring⟩)
    · simp only [mem_filter, mem_univ, true_and, kerL] at hy ⊢
      have h1 := linMap_add κ (y - x) x
      rw [sub_add_cancel] at h1
      have h2 : linMap κ y = linMap κ x := add_left_cancel hy
      rw [h2] at h1
      exact (add_eq_right.mp h1.symm)
    · simp only [mem_filter, mem_univ, true_and, kerL] at hz ⊢
      rw [linMap_add, hz, zero_add]
  have hcardK : (kerL (F := F) κ).card = 2 ^ (EuclideanDomain.gcd κ (X ^ m - 1)).natDegree := by
    rw [kerL_gcd hcard]; exact card_kerL_of_dvd hcard hm hg
  constructor
  · rintro ⟨hz, h2⟩
    have hdeg : (EuclideanDomain.gcd κ (X ^ m - 1)).natDegree = 1 := by
      have := h2 0; rw [hfib, hcardK] at this
      exact Nat.pow_right_injective (le_refl 2) (by simpa using this)
    refine ⟨?_, eq_X_add_one_of_dvd hm hg hdeg⟩
    have h0 := hz 0
    rw [linMap_zero, add_zero] at h0
    rcases zmod2_cases ε with rfl | rfl
    · exact absurd (map_zero (c2 F)) h0
    · rfl
  · rintro ⟨rfl, hgcd⟩
    have hd1 : ((X : (ZMod 2)[X]) + 1).natDegree = 1 := by rw [← C_1]; exact natDegree_X_add_C 1
    refine ⟨fun x hx => ?_, fun x => by rw [hfib, hcardK, hgcd, hd1, pow_one]⟩
    obtain ⟨w, hw⟩ := EuclideanDomain.gcd_dvd_left κ ((X : (ZMod 2)[X]) ^ m - 1)
    rw [hgcd] at hw
    have hval : linMap κ x = 1 := by
      rw [map_one] at hx
      calc linMap κ x = 1 + (1 + linMap κ x) := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        _ = 1 := by rw [hx, add_zero]
    have htr : absTr m (linMap κ x) = 0 := by
      rw [hw, linMap_mul, linMap_add_poly, linMap_X, linMap_one]
      exact absTr_sq_add hcard _
    rw [hval, absTr_one_of_odd hmodd] at htr
    exact one_ne_zero htr

/-! ### From a quadratic polynomial to `ε + κ(σ)` (display (1) of the paper) -/

/-- Support of a quadratic polynomial (constant, linearised and DO terms) for exponents below `2^m`. -/
def IsQuadSupp (m : ℕ) (p : (ZMod 2)[X]) : Prop :=
  ∀ n ∈ p.support, n = 0 ∨ (∃ i < m, n = 2 ^ i) ∨ ∃ i j, i < j ∧ j < m ∧ n = 2 ^ i + 2 ^ j

/-- `κ = ∑_{1 ≤ j < m} [X^(1+2^j)]p · t^j`. -/
noncomputable def kappaOf (m : ℕ) (p : (ZMod 2)[X]) : (ZMod 2)[X] :=
  ∑ j ∈ Ico 1 m, monomial j (p.coeff (1 + 2 ^ j))

theorem linMap_sum {ι : Type*} (s : Finset ι) (f : ι → (ZMod 2)[X]) (x : F) :
    linMap (∑ i ∈ s, f i) x = ∑ i ∈ s, linMap (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linMap_zero_poly]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, linMap_add_poly, ih]

theorem natCast_succ_zmod2 (n : ℕ) : ((n : ZMod 2) + 1) = (((n + 1) % 2 : ℕ) : ZMod 2) := by
  rw [ZMod.natCast_mod]; push_cast; ring

/-- Display (1) of the paper for `𝔽_2` coefficients: `p' = ε + ∑_{1 ≤ j < m} [X^(1+2^j)]p · X^(2^j)`. -/
theorem derivative_quadratic {m : ℕ} {p : (ZMod 2)[X]} (hq : IsQuadSupp m p) :
    derivative p = C (p.coeff 1) + ∑ j ∈ Ico 1 m, C (p.coeff (1 + 2 ^ j)) * X ^ (2 ^ j) := by
  ext n
  simp only [coeff_derivative, coeff_add, coeff_C, finsetSum_coeff, coeff_C_mul, coeff_X_pow,
    mul_ite, mul_one, mul_zero]
  rw [natCast_succ_zmod2]
  have hpow1 : ∀ j, 1 ≤ j → 2 ∣ 2 ^ j := fun j hj => dvd_pow_self 2 (by omega)
  by_cases hc : p.coeff (n + 1) = 0
  · rw [hc, zero_mul]
    have h0 : (if n = 0 then p.coeff 1 else 0) = 0 := by
      split_ifs with h; · subst h; simpa using hc
      · rfl
    rw [h0, zero_add]
    refine (sum_eq_zero (fun j _ => ?_)).symm
    split_ifs with h; · rw [show 1 + 2 ^ j = n + 1 by omega, hc]
    · rfl
  · have hmem : n + 1 ∈ p.support := mem_support_iff.mpr hc
    rcases hq _ hmem with h | ⟨i, him, hi⟩ | ⟨i, j, hij, hjm, hi⟩
    · omega
    · rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have hn : n = 0 := by simpa using hi
        subst hn
        rw [show (0 + 1) % 2 = 1 by rfl, Nat.cast_one, mul_one, if_pos rfl]
        have hs : ∑ j ∈ Ico 1 m, (if 0 = 2 ^ j then p.coeff (1 + 2 ^ j) else 0) = 0 := by
          refine sum_eq_zero (fun j hj => ?_)
          have : 2 ≤ 2 ^ j := by
            have := (mem_Ico.mp hj).1
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) this
          rw [if_neg (by omega)]
        rw [hs, add_zero]
      · have hd := hpow1 i hipos
        have hev : (n + 1) % 2 = 0 := by omega
        rw [hev, Nat.cast_zero, mul_zero]
        have hn0 : n ≠ 0 := by
          intro h; subst h
          have : 2 ≤ 2 ^ i := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hipos
          omega
        rw [if_neg hn0, zero_add]
        refine (sum_eq_zero (fun j hj => ?_)).symm
        have hd' := hpow1 j (mem_Ico.mp hj).1
        rw [if_neg (by omega)]
    · rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have hn : n = 2 ^ j := by simp at hi; omega
        have hj1 : 1 ≤ j := by omega
        have hd := hpow1 j hj1
        have hodd : (n + 1) % 2 = 1 := by omega
        rw [hodd, Nat.cast_one, mul_one]
        have hn0 : n ≠ 0 := by rw [hn]; positivity
        rw [if_neg hn0, zero_add, sum_eq_single j]
        · rw [if_pos hn, show 1 + 2 ^ j = n + 1 by omega]
        · intro j' _ hj'
          rw [if_neg]
          intro h; exact hj' (Nat.pow_right_injective (le_refl 2) (h.symm.trans hn))
        · intro h; exact absurd (mem_Ico.mpr ⟨hj1, hjm⟩) h
      · have hdi := hpow1 i hipos
        have hdj := hpow1 j (by omega)
        have hev : (n + 1) % 2 = 0 := by omega
        rw [hev, Nat.cast_zero, mul_zero]
        have hn0 : n ≠ 0 := by
          intro h; subst h
          have : 2 ≤ 2 ^ i := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hipos
          omega
        rw [if_neg hn0, zero_add]
        refine (sum_eq_zero (fun j' hj' => ?_)).symm
        have hd' := hpow1 j' (mem_Ico.mp hj').1
        rw [if_neg (by omega)]

theorem eval_derivative_quadratic {m : ℕ} {p : (ZMod 2)[X]} (hq : IsQuadSupp m p) (x : F) :
    (derivative (p.map (c2 F))).eval x = c2 F (p.coeff 1) + linMap (kappaOf m p) x := by
  rw [derivative_map, derivative_quadratic hq, kappaOf, linMap_sum]
  simp only [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
    map_C, map_X, eval_add, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, linMap_monomial]

/-- **Lemma 2.2.** Let `p` be a quadratic polynomial with coefficients in `𝔽_2` (exponents `0`, `2^i`,
`2^i + 2^j` with `i < j < m`) and `κ = ∑_{j ≥ 1} [X^(1+2^j)]p · t^j`. Over `F = 𝔽_{2^m}`, `m` odd, `p` is
derivative-optimal iff `ε = [X]p = 1` and `gcd(κ, t^m - 1) = t + 1`. -/
theorem lemma_2_2 {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (hmodd : Odd m) {p : (ZMod 2)[X]}
    (hq : IsQuadSupp m p) :
    IsDerivOptimal (p.map (c2 F)) ↔
      p.coeff 1 = 1 ∧ EuclideanDomain.gcd (kappaOf m p) (X ^ m - 1) = X + 1 := by
  unfold IsDerivOptimal
  simp only [eval_derivative_quadratic hq]
  exact lemma_2_2_core hcard hmodd _ _

end ResidueAPN
