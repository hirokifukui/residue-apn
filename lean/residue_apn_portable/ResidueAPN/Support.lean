import ResidueAPN.ThmA

/-!
# Theorem 3.1(1) of paper_R5 — support, term count, degree

`P_{m,r} = ∑_{e ∈ S} X^e` in every commutative ring, where `S = expOf '' I` and `I` is the set of
binary index sets
`{i} (i ≤ r-2)`, `{i, r-2} (i < r-2)`, `{i, m-2} (i < r-2)`, `{r-2, m-2}`, `{r-2, m-1}`, `{m-2, m-1}`,
`expOf s = ∑_{i ∈ s} 2^i`. Hence all coefficients are `0` or `1`, there are exactly `3r - 2`
terms, every exponent is `< 2^m`, and the degree is `3 · 2^(m-2)`.
-/

namespace ResidueAPN

open Polynomial Finset

/-- The exponent with binary index set `s`. -/
def expOf (s : Finset ℕ) : ℕ := ∑ i ∈ s, 2 ^ i

theorem expOf_injective : Function.Injective expOf := by
  intro s t h
  have hs := Finset.toFinset_bitIndices_sum_two_pow s
  have ht := Finset.toFinset_bitIndices_sum_two_pow t
  unfold expOf at h
  rw [← hs, ← ht, h]

theorem expOf_singleton (i : ℕ) : expOf {i} = 2 ^ i := by simp [expOf]

theorem expOf_pair {a b : ℕ} (h : a ≠ b) : expOf {a, b} = 2 ^ a + 2 ^ b := by
  simp [expOf, Finset.sum_pair h]

/-- The four blocks of index sets. -/
def idx1 (r : ℕ) : Finset (Finset ℕ) := (range (r - 1)).image (fun i => {i})
def idx2 (r : ℕ) : Finset (Finset ℕ) := (range (r - 2)).image (fun i => {i, r - 2})
def idx3 (m r : ℕ) : Finset (Finset ℕ) := (range (r - 2)).image (fun i => {i, m - 2})
def idx4 (m r : ℕ) : Finset (Finset ℕ) := {{r - 2, m - 2}, {r - 2, m - 1}, {m - 2, m - 1}}

def supportIdx (m r : ℕ) : Finset (Finset ℕ) := idx1 r ∪ idx2 r ∪ idx3 m r ∪ idx4 m r

/-- The support of `P_{m,r}`. -/
def suppP (m r : ℕ) : Finset ℕ := (supportIdx m r).image expOf

section Combinatorics

variable {m r : ℕ}

theorem mem_of_eq_left {s t : Finset ℕ} (h : s = t) {x : ℕ} (hx : x ∈ s) : x ∈ t := h ▸ hx

set_option hygiene false in
/-- Separate two explicit pair sets: try each candidate element on each side. -/
macro "sep_pair " h:ident : tactic => `(tactic| first
  | (have e := mem_of_eq_left $h (x := a) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega)
  | (have e := mem_of_eq_left $h (x := i) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega)
  | (have e := mem_of_eq_left $h (x := r - 2) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega)
  | (have e := mem_of_eq_left $h (x := m - 2) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega)
  | (have e := mem_of_eq_left $h (x := m - 1) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega)
  | (have e := mem_of_eq_left ($h).symm (x := b) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega)
  | (have e := mem_of_eq_left ($h).symm (x := r - 2) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega)
  | (have e := mem_of_eq_left ($h).symm (x := m - 2) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega)
  | (have e := mem_of_eq_left ($h).symm (x := m - 1) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at e; omega))

theorem card_idx1 : (idx1 r).card = r - 1 := by
  rw [idx1, card_image_of_injective _ (fun a b h => Finset.singleton_injective h), card_range]

theorem card_idx2 (hr : 3 ≤ r) : (idx2 r).card = r - 2 := by
  rw [idx2, card_image_of_injOn, card_range]
  intro a ha b hb h
  simp only [coe_range, Set.mem_Iio] at ha hb
  sep_pair h

theorem card_idx3 (hr : 3 ≤ r) (hrm : r < m) : (idx3 m r).card = r - 2 := by
  rw [idx3, card_image_of_injOn, card_range]
  intro a ha b hb h
  simp only [coe_range, Set.mem_Iio] at ha hb
  sep_pair h

theorem card_idx4 (hr : 3 ≤ r) (hrm : r < m) : (idx4 m r).card = 3 := by
  rw [idx4, card_insert_of_notMem, card_pair]
  · intro h
    sep_pair h
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with h | h
    · sep_pair h
    · sep_pair h

theorem card_of_mem_idx1 {s : Finset ℕ} (h : s ∈ idx1 r) : s.card = 1 := by
  simp only [idx1, mem_image] at h; obtain ⟨i, _, rfl⟩ := h; simp

theorem card_of_mem_idx2 (hr : 3 ≤ r) {s : Finset ℕ} (h : s ∈ idx2 r) : s.card = 2 := by
  simp only [idx2, mem_image, mem_range] at h; obtain ⟨i, hi, rfl⟩ := h
  exact card_pair (by omega)

theorem card_of_mem_idx3 (hr : 3 ≤ r) (hrm : r < m) {s : Finset ℕ} (h : s ∈ idx3 m r) :
    s.card = 2 := by
  simp only [idx3, mem_image, mem_range] at h; obtain ⟨i, hi, rfl⟩ := h
  exact card_pair (by omega)

theorem card_of_mem_idx4 (hr : 3 ≤ r) (hrm : r < m) {s : Finset ℕ} (h : s ∈ idx4 m r) :
    s.card = 2 := by
  simp only [idx4, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl <;> exact card_pair (by omega)

/-- Membership facts used to separate the blocks: `m-2` and `m-1` lie in no set of block 2. -/
theorem notMem_idx2 (hr : 3 ≤ r) (hrm : r < m) {s : Finset ℕ} (h : s ∈ idx2 r) {x : ℕ}
    (hx : r - 2 < x) : x ∉ s := by
  simp only [idx2, mem_image, mem_range] at h; obtain ⟨i, hi, rfl⟩ := h
  simp only [mem_insert, mem_singleton]; omega

theorem disj12 (hr : 3 ≤ r) : Disjoint (idx1 r) (idx2 r) := by
  rw [disjoint_left]; intro s h1 h2
  have := card_of_mem_idx1 h1; have := card_of_mem_idx2 hr h2; omega

theorem disj_123 (hr : 3 ≤ r) (hrm : r < m) : Disjoint (idx1 r ∪ idx2 r) (idx3 m r) := by
  rw [disjoint_left]; intro s h12 h3
  rcases mem_union.mp h12 with h1 | h2
  · have := card_of_mem_idx1 h1; have := card_of_mem_idx3 hr hrm h3; omega
  · have hm : m - 2 ∈ s := by
      simp only [idx3, mem_image, mem_range] at h3; obtain ⟨i, _, rfl⟩ := h3; simp
    exact notMem_idx2 hr hrm h2 (by omega) hm

theorem disj_1234 (hr : 3 ≤ r) (hrm : r < m) :
    Disjoint (idx1 r ∪ idx2 r ∪ idx3 m r) (idx4 m r) := by
  rw [disjoint_left]; intro s h123 h4
  rcases mem_union.mp h123 with h12 | h3
  · rcases mem_union.mp h12 with h1 | h2
    · have := card_of_mem_idx1 h1; have := card_of_mem_idx4 hr hrm h4; omega
    · simp only [idx4, mem_insert, mem_singleton] at h4
      rcases h4 with rfl | rfl | rfl
      · exact notMem_idx2 hr hrm h2 (x := m - 2) (by omega) (by simp)
      · exact notMem_idx2 hr hrm h2 (x := m - 1) (by omega) (by simp)
      · exact notMem_idx2 hr hrm h2 (x := m - 1) (by omega) (by simp)
  · simp only [idx3, mem_image, mem_range] at h3; obtain ⟨i, hi, rfl⟩ := h3
    simp only [idx4, mem_insert, mem_singleton] at h4
    rcases h4 with h | h | h
    · sep_pair h
    · sep_pair h
    · sep_pair h

/-- **Theorem 3.1(1): exactly `3r - 2` terms.** -/
theorem card_suppP (hr : 3 ≤ r) (hrm : r < m) : (suppP m r).card = 3 * r - 2 := by
  rw [suppP, card_image_of_injective _ expOf_injective, supportIdx,
    card_union_of_disjoint (disj_1234 hr hrm), card_union_of_disjoint (disj_123 hr hrm),
    card_union_of_disjoint (disj12 hr), card_idx1, card_idx2 hr, card_idx3 hr hrm, card_idx4 hr hrm]
  omega

/-- Every exponent of `P_{m,r}` is below `2^m`, and the largest is `3 · 2^(m-2)`. -/
theorem lt_of_mem_suppP (hr : 3 ≤ r) (hrm : r < m) {e : ℕ} (he : e ∈ suppP m r) :
    e ≤ 3 * 2 ^ (m - 2) := by
  have hpow : ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := fun h => Nat.pow_le_pow_right (by norm_num) h
  have hm1 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by rw [← pow_succ']; congr 1; omega
  simp only [suppP, supportIdx, mem_image, mem_union] at he
  obtain ⟨s, hs, rfl⟩ := he
  rcases hs with ((h1 | h2) | h3) | h4
  · simp only [idx1, mem_image, mem_range] at h1; obtain ⟨i, hi, rfl⟩ := h1
    rw [expOf_singleton]; have := hpow (show i ≤ m - 2 by omega); omega
  · simp only [idx2, mem_image, mem_range] at h2; obtain ⟨i, hi, rfl⟩ := h2
    rw [expOf_pair (by omega)]
    have := hpow (show i ≤ m - 2 by omega); have := hpow (show r - 2 ≤ m - 2 by omega); omega
  · simp only [idx3, mem_image, mem_range] at h3; obtain ⟨i, hi, rfl⟩ := h3
    rw [expOf_pair (by omega)]; have := hpow (show i ≤ m - 2 by omega); omega
  · simp only [idx4, mem_insert, mem_singleton] at h4
    rcases h4 with rfl | rfl | rfl
    · rw [expOf_pair (by omega)]; have := hpow (show r - 2 ≤ m - 2 by omega); omega
    · rw [expOf_pair (by omega)]; have := hpow (show r - 2 ≤ m - 2 by omega); omega
    · rw [expOf_pair (by omega)]; omega

theorem top_mem_suppP (hr : 3 ≤ r) (hrm : r < m) : 3 * 2 ^ (m - 2) ∈ suppP m r := by
  refine mem_image.mpr ⟨{m - 2, m - 1}, ?_, ?_⟩
  · simp [supportIdx, idx4]
  · rw [expOf_pair (by omega), show m - 1 = (m - 2) + 1 by omega, pow_succ]; ring

end Combinatorics

section Expansion

variable {R : Type*} [CommRing R] {m r : ℕ}

theorem sum_idx_image (s : Finset (Finset ℕ)) :
    ∑ e ∈ s.image expOf, (X : R[X]) ^ e = ∑ t ∈ s, X ^ expOf t :=
  sum_image (fun a _ b _ h => expOf_injective h)

/-- **Theorem 3.1(1): `P_{m,r} = ∑_{e ∈ S} X^e`.** In particular every coefficient is `0` or `1`. -/
theorem polP_eq_sum_supp (hr : 3 ≤ r) (hrm : r < m) :
    polP R m r = ∑ e ∈ suppP m r, X ^ e := by
  rw [suppP, sum_idx_image, supportIdx, sum_union (disj_1234 hr hrm), sum_union (disj_123 hr hrm),
    sum_union (disj12 hr)]
  have e1 : ∑ t ∈ idx1 r, (X : R[X]) ^ expOf t = polV R r + polW R r := by
    rw [idx1, sum_image (fun a _ b _ h => Finset.singleton_injective h), polV, polW,
      show r - 1 = (r - 2) + 1 by omega, sum_range_succ]
    simp [expOf_singleton]
  have e2 : ∑ t ∈ idx2 r, (X : R[X]) ^ expOf t = polW R r * polV R r := by
    rw [idx2, sum_image, polV, polW, mul_sum]
    · refine sum_congr rfl (fun i hi => ?_)
      simp only [mem_range] at hi
      rw [expOf_pair (by omega), pow_add, mul_comm]
    · intro a ha b hb h
      simp only [coe_range, Set.mem_Iio] at ha hb
      sep_pair h
  have e3 : ∑ t ∈ idx3 m r, (X : R[X]) ^ expOf t = polY R m * polV R r := by
    rw [idx3, sum_image, polV, polY, mul_sum]
    · refine sum_congr rfl (fun i hi => ?_)
      simp only [mem_range] at hi
      rw [expOf_pair (by omega), pow_add, mul_comm]
    · intro a ha b hb h
      simp only [coe_range, Set.mem_Iio] at ha hb
      sep_pair h
  have e4 : ∑ t ∈ idx4 m r, (X : R[X]) ^ expOf t
      = polW R r * polY R m + polW R r * polZ R m + polY R m * polZ R m := by
    have h1 : ({r - 2, m - 2} : Finset ℕ) ∉ ({{r - 2, m - 1}, {m - 2, m - 1}} : Finset (Finset ℕ)) := by
      intro h
      simp only [mem_insert, mem_singleton] at h
      rcases h with h | h
      · sep_pair h
      · sep_pair h
    have h2 : ({r - 2, m - 1} : Finset ℕ) ≠ {m - 2, m - 1} := by
      intro h; sep_pair h
    rw [idx4, sum_insert h1, sum_pair h2, expOf_pair (by omega), expOf_pair (by omega),
      expOf_pair (by omega), polW, polY, polZ, pow_add, pow_add, pow_add]
    ring
  rw [e1, e2, e3, e4, polP]
  ring

/-- The coefficients of `P_{m,r}` are `1` on `S` and `0` elsewhere. -/
theorem coeff_polP (hr : 3 ≤ r) (hrm : r < m) (e : ℕ) :
    (polP R m r).coeff e = if e ∈ suppP m r then 1 else 0 := by
  rw [polP_eq_sum_supp hr hrm, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [sum_ite_eq]

/-- **Theorem 3.1(1): degree `3q/4`.** -/
theorem natDegree_polP [Nontrivial R] (hr : 3 ≤ r) (hrm : r < m) :
    (polP R m r).natDegree = 3 * 2 ^ (m - 2) := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro e he
    rw [coeff_polP hr hrm, if_neg]
    intro hmem
    have := lt_of_mem_suppP hr hrm hmem
    exact absurd he (not_lt.mpr (by exact_mod_cast this))
  · apply le_natDegree_of_ne_zero
    rw [coeff_polP hr hrm, if_pos (top_mem_suppP hr hrm)]
    exact one_ne_zero

end Expansion

end ResidueAPN
