import Mathlib

/-!
# APN2 R03 — first-stage formal lemmas (Claude, 2026-10-25)

L1 `Drho_surj`      : D_ρ h = h(·+ρ) + h maps onto ρ-periodic functions (ρ ≠ 0, ρ+ρ = 0; values in a group of exponent 2).
L2 `quad_fiber`     : in a field of characteristic 2 with μ ≠ 0, μy²+Ay = μz²+Az ↔ z = y ∨ z = y + A/μ.
L3 `coset_dichotomy`: c+H and c+E+H coincide if E ∈ H and are disjoint otherwise.
L4 `absTr_artin_schreier` : in a finite field of order 2^m, Tr(t²+t) = 0 for Tr x = Σ_{i<m} x^(2^i).

These are abstract lemmas.  They are NOT a formalization of the Galois-ring theorems (mod 8 stability,
spectra, minimax); see the correspondence table in LEAN_REPORT_R03.md.
-/

set_option linter.unusedSectionVars false

namespace APN2R03

open Finset

section L1
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

/-- The pair relation `b = a ∨ b = a + ρ` (an equivalence since ρ + ρ = 0). -/
def pairSetoid (ρ : G) (hρ2 : ρ + ρ = 0) : Setoid G where
  r a b := b = a ∨ b = a + ρ
  iseqv := by
    refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
    · rintro a b (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, add_assoc, hρ2, add_zero])
    · rintro a b c (h1 | h1) (h2 | h2)
      · exact Or.inl (by rw [h2, h1])
      · exact Or.inr (by rw [h2, h1])
      · exact Or.inr (by rw [h2, h1])
      · exact Or.inl (by rw [h2, h1, add_assoc, hρ2, add_zero])

theorem Drho_surj (ρ : G) (hρ : ρ ≠ 0) (hρ2 : ρ + ρ = 0)
    (f : G → M) (hf : ∀ a, f (a + ρ) = f a) :
    ∃ h : G → M, ∀ a, h (a + ρ) + h a = f a := by
  classical
  letI : Setoid G := pairSetoid ρ hρ2
  let out : G → G := fun a => (⟦a⟧ : Quotient (pairSetoid ρ hρ2)).out
  have hout : ∀ a, out a = a ∨ out a = a + ρ := by
    intro a
    have h : a = out a ∨ a = out a + ρ := Quotient.mk_out a
    rcases h with h | h
    · exact Or.inl h.symm
    · right
      calc out a = out a + ρ + ρ := by rw [add_assoc, hρ2, add_zero]
        _ = a + ρ := by rw [← h]
  have hshift : ∀ a, out (a + ρ) = out a := by
    intro a
    have hq : (⟦a + ρ⟧ : Quotient (pairSetoid ρ hρ2)) = ⟦a⟧ :=
      Quotient.sound (show a = a + ρ ∨ a = a + ρ + ρ from
        Or.inr (by rw [add_assoc, hρ2, add_zero]))
    simp only [out, hq]
  have hne : ∀ a : G, a + ρ ≠ a := by
    intro a h
    apply hρ
    have := congrArg (fun x => x - a) h
    simpa using this
  refine ⟨fun a => if out a = a then f a else 0, ?_⟩
  intro a
  rcases hout a with h1 | h1
  · have h2 : ¬ (out (a + ρ) = a + ρ) := by
      rw [hshift, h1]; exact fun h => hne a h.symm
    show (if out (a + ρ) = a + ρ then f (a + ρ) else 0) + (if out a = a then f a else 0) = f a
    rw [if_neg h2, if_pos h1, zero_add]
  · have h2 : out (a + ρ) = a + ρ := by rw [hshift, h1]
    have h3 : ¬ (out a = a) := by rw [h1]; exact hne a
    show (if out (a + ρ) = a + ρ then f (a + ρ) else 0) + (if out a = a then f a else 0) = f a
    rw [if_pos h2, if_neg h3, add_zero, hf]

end L1

section L2
variable {F : Type*} [Field F] [CharP F 2]

theorem quad_fiber (μ A y z : F) (hμ : μ ≠ 0) :
    μ * y ^ 2 + A * y = μ * z ^ 2 + A * z ↔ z = y ∨ z = y + A / μ := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hd : μ * (A / μ) = A := by field_simp
  constructor
  · intro h
    have h2 : (z - y) * (μ * (z + y) + A) = 0 := by linear_combination (-1 : F) * h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; exact sub_eq_zero.mp h3
    · right
      have h4 : z + y = A / μ := by
        rw [eq_div_iff hμ]
        linear_combination h3 - (A) * two
      linear_combination h4 - y * two
  · rintro (h | h)
    · rw [h]
    · rw [h]
      linear_combination (-(A / μ)) * hd + (-((A / μ) * (μ * y + A))) * two

end L2

section L3

theorem coset_dichotomy {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (c E x : G) :
    (E ∈ H → (x - c ∈ H ↔ x - (c + E) ∈ H)) ∧
    (E ∉ H → ¬ (x - c ∈ H ∧ x - (c + E) ∈ H)) := by
  have key : x - (c + E) = (x - c) - E := by abel
  refine ⟨fun hE => ?_, fun hE h => ?_⟩
  · rw [key]
    constructor
    · intro h; exact H.sub_mem h hE
    · intro h
      have := H.add_mem h hE
      simpa using this
  · apply hE
    have h2 : (x - c) - E ∈ H := key ▸ h.2
    have := H.sub_mem h.1 h2
    simpa using this

end L3

section L4
variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

/-- The absolute trace written as a sum of Frobenius powers. -/
def absTr (m : ℕ) (x : K) : K := ∑ i ∈ range m, x ^ (2 ^ i)

theorem absTr_artin_schreier (m : ℕ) (hcard : Fintype.card K = 2 ^ m) (t : K) :
    absTr m (t ^ 2 + t) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold absTr
  have hfrob : ∀ i : ℕ, (t ^ 2 + t) ^ (2 ^ i) = t ^ (2 ^ (i + 1)) + t ^ (2 ^ i) := by
    intro i
    rw [add_pow_char_pow, ← pow_mul, ← pow_succ']
  simp_rw [hfrob]
  have tele : ∀ n : ℕ, ∑ i ∈ range n, (t ^ (2 ^ (i + 1)) + t ^ (2 ^ i)) = t ^ (2 ^ n) + t := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, pow_one]
      linear_combination (-t) * two
    | succ n ih =>
      rw [sum_range_succ, ih]
      linear_combination (t ^ (2 ^ n)) * two
  rw [tele, ← hcard, FiniteField.pow_card]
  linear_combination t * two

end L4


/-! ## R03 second stage (Claude, 2026-10-25)
L5 `absTr_eq_zero_iff` : image of t ↦ t²+t equals the trace kernel (both directions).
L6 `chi_criterion`     : for μ,A ≠ 0, E ∈ Im(μy²+Ay) ↔ Tr(μE/A²) = 0.
L7 `local_pair_count`  : the per-pair counts used in the k = 3 spectrum (S1).
L8 mod-4 ring identities: binomial congruence, A for r = 3 and r ≥ 5, the E_nat numerator.
L9 `phi_identity`      : the χ ≡ 1 identity of the r = 3 correction (any ring of characteristic 2),
   and `frob_back` : t = a^(2^(m-3)) satisfies t^8 = a in a field of order 2^m.
-/

open Polynomial

section L5
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

theorem as_fiber (s t : K) : s ^ 2 + s = t ^ 2 + t ↔ s = t ∨ s = t + 1 := by
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have h' : (s - t) * (s + t + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1 - (t + 1) * two
  · rintro (rfl | rfl)
    · rfl
    · linear_combination (t + 1) * two

theorem add_one_ne (t : K) : t + 1 ≠ t := by
  intro h
  have : (1 : K) = 0 := by linear_combination h
  exact one_ne_zero this

theorem card_image_as (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card K = 2 ^ m) :
    (Finset.univ.image (fun t : K => t ^ 2 + t)).card = 2 ^ (m - 1) := by
  have key := Finset.card_eq_sum_card_image (fun t : K => t ^ 2 + t) (Finset.univ : Finset K)
  have hfib : ∀ a ∈ Finset.univ.image (fun t : K => t ^ 2 + t),
      (Finset.univ.filter (fun x : K => x ^ 2 + x = a)).card = 2 := by
    intro a ha
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp ha
    have : Finset.univ.filter (fun x : K => x ^ 2 + x = t ^ 2 + t) = {t, t + 1} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact as_fiber s t
    rw [this, Finset.card_pair (add_one_ne t).symm]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, Finset.card_univ, hcard] at key
  have h2 : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  omega

theorem card_absTr_ker_le (m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.filter (fun x : K => absTr m x = 0)).card ≤ 2 ^ (m - 1) := by
  set P : K[X] := ∑ i ∈ range m, (X : K[X]) ^ (2 ^ i) with hPdef
  have hev : ∀ x, P.eval x = absTr m x := by
    intro x; simp [P, absTr, eval_finsetSum]
  have hc1 : P.coeff 1 = 1 := by
    simp only [P, finsetSum_coeff, coeff_X_pow]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      have h2b : 2 ≤ 2 ^ b := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hb)
      have : (1 : ℕ) ≠ 2 ^ b := by omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hP : P ≠ 0 := by
    intro h; rw [h] at hc1; simp at hc1
  have hdeg : P.natDegree ≤ 2 ^ (m - 1) := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    rw [natDegree_X_pow]
    exact Nat.pow_le_pow_right (by norm_num) (by have := Finset.mem_range.mp hi; omega)
  calc (Finset.univ.filter (fun x : K => absTr m x = 0)).card
      ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, hev]
        exact hx
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ 2 ^ (m - 1) := hdeg

theorem absTr_eq_zero_iff (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card K = 2 ^ m) (x : K) :
    absTr m x = 0 ↔ ∃ t : K, t ^ 2 + t = x := by
  have hsub : Finset.univ.image (fun t : K => t ^ 2 + t) ⊆
      Finset.univ.filter (fun x : K => absTr m x = 0) := by
    intro y hy
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact absTr_artin_schreier m hcard t
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [card_image_as m hm hcard]; exact card_absTr_ker_le m hm)
  constructor
  · intro hx
    have hmem : x ∈ Finset.univ.filter (fun x : K => absTr m x = 0) := by simp [hx]
    rw [← heq] at hmem
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hmem
    exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩
    exact absTr_artin_schreier m hcard t

end L5

section L6
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

theorem chi_criterion (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card K = 2 ^ m)
    (μ A E : K) (hμ : μ ≠ 0) (hA : A ≠ 0) :
    (∃ y : K, μ * y ^ 2 + A * y = E) ↔ absTr m (μ * E / A ^ 2) = 0 := by
  rw [absTr_eq_zero_iff m hm hcard]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨μ * y / A, ?_⟩
    field_simp
  · rintro ⟨s, hs⟩
    refine ⟨A * s / μ, ?_⟩
    have hE : E = A ^ 2 * (s ^ 2 + s) / μ := by
      rw [hs]; field_simp
    rw [hE]
    field_simp

end L6

section L7
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- number of solutions of μy²+Ay = c -/
def nfib (μ A c : K) : ℕ := (Finset.univ.filter (fun y : K => μ * y ^ 2 + A * y = c)).card

/-- the image of y ↦ μy²+Ay -/
def qimg (μ A : K) : Finset K := Finset.univ.image (fun y : K => μ * y ^ 2 + A * y)

theorem nfib_eq (μ A c : K) (hμ : μ ≠ 0) (hA : A ≠ 0) :
    nfib μ A c = if c ∈ qimg μ A then 2 else 0 := by
  unfold nfib qimg
  split_ifs with hc
  · obtain ⟨y0, -, rfl⟩ := Finset.mem_image.mp hc
    have hne : y0 + A / μ ≠ y0 := by
      intro h
      have : A / μ = 0 := by linear_combination h
      exact div_ne_zero hA hμ this
    have : Finset.univ.filter (fun y : K => μ * y ^ 2 + A * y = μ * y0 ^ 2 + A * y0) =
        {y0, y0 + A / μ} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [eq_comm]
      exact quad_fiber μ A y0 z hμ
    rw [this, Finset.card_pair hne.symm]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    exact hc (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hy⟩)

theorem qmap_add (μ A y z : K) :
    μ * (y + z) ^ 2 + A * (y + z) = (μ * y ^ 2 + A * y) + (μ * z ^ 2 + A * z) := by
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (μ * y * z) * two

theorem card_qimg (m : ℕ) (hcard : Fintype.card K = 2 ^ m) (μ A : K) (hμ : μ ≠ 0) (hA : A ≠ 0) :
    (qimg μ A).card * 2 = 2 ^ m := by
  have key := Finset.card_eq_sum_card_image (fun y : K => μ * y ^ 2 + A * y) (Finset.univ : Finset K)
  have hfib : ∀ c ∈ qimg μ A,
      (Finset.univ.filter (fun y : K => μ * y ^ 2 + A * y = c)).card = 2 := by
    intro c hc
    have := nfib_eq μ A c hμ hA
    rw [if_pos hc] at this
    exact this
  rw [Finset.card_univ, hcard] at key
  unfold qimg at hfib ⊢
  rw [key, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

theorem local_pair_count (m : ℕ) (hcard : Fintype.card K = 2 ^ m)
    (μ A E : K) (hμ : μ ≠ 0) (hA : A ≠ 0) :
    (E ∈ qimg μ A → ∀ c, nfib μ A c + nfib μ A (c + E) = if c ∈ qimg μ A then 4 else 0) ∧
    (E ∉ qimg μ A → ∀ c, nfib μ A c + nfib μ A (c + E) = 2) := by
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  have memq : ∀ c, c ∈ qimg μ A ↔ ∃ y, μ * y ^ 2 + A * y = c := by
    intro c; unfold qimg; simp
  -- closure facts
  have hshift : E ∈ qimg μ A → ∀ c, (c + E ∈ qimg μ A ↔ c ∈ qimg μ A) := by
    intro hE c
    obtain ⟨e, he⟩ := (memq E).mp hE
    constructor
    · intro h
      obtain ⟨y, hy⟩ := (memq _).mp h
      exact (memq c).mpr ⟨y + e, by rw [qmap_add, hy, he]; linear_combination E * two⟩
    · intro h
      obtain ⟨y, hy⟩ := (memq _).mp h
      exact (memq _).mpr ⟨y + e, by rw [qmap_add, hy, he]⟩
  have hdisj : E ∉ qimg μ A → ∀ c, ¬ (c ∈ qimg μ A ∧ c + E ∈ qimg μ A) := by
    intro hE c ⟨h1, h2⟩
    obtain ⟨y1, hy1⟩ := (memq _).mp h1
    obtain ⟨y2, hy2⟩ := (memq _).mp h2
    exact hE ((memq E).mpr ⟨y1 + y2, by rw [qmap_add, hy1, hy2]; linear_combination c * two⟩)
  refine ⟨fun hE c => ?_, fun hE c => ?_⟩
  · rw [nfib_eq μ A c hμ hA, nfib_eq μ A (c + E) hμ hA]
    by_cases hc : c ∈ qimg μ A
    · rw [if_pos hc, if_pos ((hshift hE c).mpr hc), if_pos hc]
    · rw [if_neg hc, if_neg (fun h => hc ((hshift hE c).mp h)), if_neg hc]
  · -- the image and its translate are disjoint and together have 2^m elements: they cover K
    have hcover : ∀ c, c ∈ qimg μ A ∨ c + E ∈ qimg μ A := by
      set T := (qimg μ A).image (fun c => c + E) with hT
      have hTc : T.card = (qimg μ A).card :=
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)
      have hD : Disjoint (qimg μ A) T := by
        rw [Finset.disjoint_left]
        intro a ha haT
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp haT
        exact hdisj hE b ⟨hb, ha⟩
      have hU : (qimg μ A ∪ T).card = 2 ^ m := by
        rw [Finset.card_union_of_disjoint hD, hTc]
        have := card_qimg m hcard μ A hμ hA
        omega
      have hall : qimg μ A ∪ T = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hU, hcard])
      intro c
      have hc : c ∈ qimg μ A ∪ T := by rw [hall]; exact Finset.mem_univ c
      rcases Finset.mem_union.mp hc with h | h
      · exact Or.inl h
      · right
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        have : b + E + E = b := by linear_combination E * two
        rw [this]; exact hb
    rw [nfib_eq μ A c hμ hA, nfib_eq μ A (c + E) hμ hA]
    rcases hcover c with h | h
    · rw [if_pos h, if_neg (fun h' => hdisj hE c ⟨h, h'⟩)]
    · rw [if_neg (fun h' => hdisj hE c ⟨h', h⟩), if_pos h]

end L7

section L8
variable {R : Type*} [CommRing R]

/-- (x+1)^(2^(j+1)) ≡ x^(2^(j+1)) + 1 + 2 x^(2^j)  (mod 4). -/
theorem binom_mod4 (h4 : (4 : R) = 0) (x : R) (j : ℕ) :
    (x + 1) ^ (2 ^ (j + 1)) = x ^ (2 ^ (j + 1)) + 1 + 2 * x ^ (2 ^ j) := by
  induction j with
  | zero => ring
  | succ j ih =>
    have e1 : (x + 1) ^ (2 ^ (j + 1 + 1)) = ((x + 1) ^ (2 ^ (j + 1))) ^ 2 := by
      rw [pow_succ 2 (j + 1), pow_mul]
    have e2 : x ^ (2 ^ (j + 1 + 1)) = (x ^ (2 ^ (j + 1))) ^ 2 := by
      rw [pow_succ 2 (j + 1), pow_mul]
    have e3 : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by
      rw [pow_succ 2 j, pow_mul]
    rw [e1, ih, e2, e3]
    linear_combination ((x ^ 2 ^ j) ^ 2 + (x ^ 2 ^ j) ^ 3 + x ^ 2 ^ j) * h4

/-- A for r = 3: with U(X+1) = U+1+2Y and V(X+1) = V+1+2U (mod 4). -/
theorem A_r3 (h4 : (4 : R) = 0) (X Y U V : R) :
    (1 + 2 * (X + 1) + 3 * (X + 1) ^ 2 + (U + 1 + 2 * Y) + 2 * (X + 1) * (U + 1 + 2 * Y)
        + 2 * (X + 1) * (V + 1 + 2 * U))
      - (1 + 2 * X + 3 * X ^ 2 + U + 2 * X * U + 2 * X * V) = 2 * (1 + X + Y + U + V) := by
  linear_combination (U * X + U + X * Y + 2 * X + Y + 2) * h4

/-- A for r ≥ 5 (W = X^w, Wh = X^(w/2), Y = X^(u/2)). -/
theorem A_r5 (h4 : (4 : R) = 0) (X Y U W Wh : R) :
    (1 + 2 * (X + 1) + (W + 1 + 2 * Wh) + 2 * (X + 1) * (W + 1 + 2 * Wh) + (U + 1 + 2 * Y)
        + 2 * (X + 1) * (U + 1 + 2 * Y))
      - (1 + 2 * X + W + 2 * X * W + U + 2 * X * U) = 2 * (Wh + W + Y + U) := by
  linear_combination (Wh * X + Wh + X * Y + X + Y + 2) * h4

/-- The E_nat numerator for r = 3: F(X+1) − F(X) − F'(X) ≡ 2·(1+X²+U+Y+XY+X²Y+X²U+YV) (mod 4),
using the exact relation U² = V. -/
theorem Enat_numerator (h4 : (4 : R) = 0) (X Y U V : R) (hUV : U ^ 2 = V) :
    ((X + 1) + (X + 1) ^ 2 + (X + 1) ^ 3 + (X + 1) * (U + 1 + 2 * Y) + (X + 1) ^ 2 * (U + 1 + 2 * Y)
        + (X + 1) ^ 2 * (V + 1 + 2 * U) + (U + 1 + 2 * Y) * (V + 1 + 2 * U))
      - (X + X ^ 2 + X ^ 3 + X * U + X ^ 2 * U + X ^ 2 * V + U * V)
      - (1 + 2 * X + 3 * X ^ 2 + U + 2 * X * U + 2 * X * V)
      = 2 * (1 + X ^ 2 + U + Y + X * Y + X ^ 2 * Y + X ^ 2 * U + Y * V) := by
  linear_combination 2 * hUV + (U * X + U * Y + U + V + X * Y + 2 * X + Y + 1) * h4

end L8

section L9

/-- χ ≡ 1 identity for the r = 3 one-term correction, with Y = t, U = t², V = t⁴, X = t⁸:
φ² + Aφ = E_new + A² in any commutative ring of characteristic 2. -/
theorem phi_identity {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (t : R) :
    let X := t ^ 8; let Y := t; let U := t ^ 2; let V := t ^ 4
    let A := 1 + X + Y + U + V
    let φ := 1 + X ^ 2 + X * V + Y * V + U * V
    let Enat := X + X ^ 2 + Y + X * Y + X ^ 2 * Y + X ^ 2 * U + V + Y * V
    let Enew := Enat + X ^ 4 + V + 1
    φ ^ 2 + A * φ = Enew + A ^ 2 := by
  intro X Y U V A φ Enat Enew
  simp only [X, Y, U, V, A, φ, Enat, Enew]
  linear_combination (t ^ 28 + t ^ 24 + t ^ 22 + t ^ 21 + t ^ 20 + t ^ 18 + t ^ 17 + t ^ 16
    + t ^ 14 + t ^ 13 + t ^ 12 + t ^ 11 - t ^ 9 - t ^ 8 + t ^ 7 + t ^ 6 - 2 * t ^ 4 - t ^ 3
    - t ^ 2 - t) * h2

/-- In a field of order 2^m (m ≥ 3), t = a^(2^(m-3)) satisfies t^8 = a, so (Y,U,V,X) = (t,t²,t⁴,t⁸). -/
theorem frob_back {K : Type*} [Field K] [Fintype K] (m : ℕ) (hm : 3 ≤ m)
    (hcard : Fintype.card K = 2 ^ m) (a : K) : (a ^ (2 ^ (m - 3))) ^ 8 = a := by
  rw [← pow_mul]
  have : 2 ^ (m - 3) * 8 = 2 ^ m := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
  rw [this, ← hcard, FiniteField.pow_card]

end L9

end APN2R03

#print axioms APN2R03.Drho_surj
#print axioms APN2R03.quad_fiber
#print axioms APN2R03.coset_dichotomy
#print axioms APN2R03.absTr_artin_schreier
#print axioms APN2R03.absTr_eq_zero_iff
#print axioms APN2R03.chi_criterion
#print axioms APN2R03.local_pair_count
#print axioms APN2R03.binom_mod4
#print axioms APN2R03.A_r3
#print axioms APN2R03.A_r5
#print axioms APN2R03.Enat_numerator
#print axioms APN2R03.phi_identity
#print axioms APN2R03.frob_back
