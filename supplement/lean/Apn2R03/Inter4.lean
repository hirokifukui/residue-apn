import Apn2R03.Inter3

/-!
# Intermediate layers, part 4: lower bounds and Theorem inter (iii) (Claude, 2026-10-26, R05c)

* `inter_lower_c3`   : a residue with `w_α(a) ≠ 0 ≠ c₃` gives an entry `≥ 2 q^(j+1)`;
* `inter_lower_deep` : `c₃ = 0 = w_α(a)` gives an entry `≥ q^(j+2)`;
* `inter_lower_pair` : `c₃ = 0`, `p^[2]` zero-free and `B_α(a) = 0` give an entry `≥ 2 q^(j+1)`;
* `exists_hasse2_ne` : for reduced `p` (`deg p < q`) with `p^[3] = c₃ ≠ 0`, `p^[2]` is not constant;
* `inter_flat_iff`   : **Theorem inter (iii)** for one direction `α = 2^j u`.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- the class count of the row of `α` at `β = α γ` -/
theorem cc_eq (f : R[X]) (j : ℕ) (hjk : j ≤ S.k) (u γ : R) (hu : S.π u ≠ 0) (a : K) :
    S.cc f (2 ^ j * u) (2 ^ j * u * γ) a = (univ.filter (fun x : R => S.π x = a ∧
      ∃ w, (Tpol f (2 ^ j * u)).eval x - γ = 2 ^ (S.k - j) * w)).card := by
  unfold cc
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Gpoly_eval]
  rw [← S.sol_iff f j hjk u γ x hu]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linear_combination h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linear_combination h2⟩

theorem roots_two (w c : K) (hw : w ≠ 0) (hc : c ≠ 0) :
    (univ.filter (fun y : K => S.π 0 + w * y + c * y ^ 2 = 0)).card = 2 := by
  have h2 := S.two_F
  have hne : (0 : K) ≠ w / c := (div_ne_zero hw hc).symm
  have hset : univ.filter (fun y : K => S.π 0 + w * y + c * y ^ 2 = 0) = ({0, w / c} : Finset K) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_zero, zero_add, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have : y * (w + c * y) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h0 | h1
      · exact Or.inl h0
      · right
        field_simp
        linear_combination h1 - w * h2
    · rintro (rfl | rfl)
      · ring
      · have : w * (w / c) + c * (w / c) ^ 2 = 2 * (w ^ 2 / c) := by field_simp; ring
        rw [this, h2, zero_mul]
  rw [hset, Finset.card_pair hne]

/-- **Lower bound** (`c₃ ≠ 0`) -/
theorem inter_lower_c3 (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (j : ℕ)
    (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) (u : R) (hu : S.π u ≠ 0) (xa : R)
    (hw : S.π ((hasseDeriv 2 f).eval xa) + S.π (2 ^ (j - 1)) * S.π u *
      S.π ((hasseDeriv 3 f).eval xa) ≠ 0)
    (hc : S.π ((hasseDeriv 3 f).eval xa) ≠ 0) :
    2 * Fintype.card K ^ (j + 1) ≤
      delta f (2 ^ j * u) (2 ^ j * u * (Tpol f (2 ^ j * u)).eval xa) := by
  have h := S.class_val hcard f j hj hjk u ((Tpol f (2 ^ j * u)).eval xa) xa 0 (by ring) hw
  rw [S.roots_two _ _ hw hc] at h
  calc 2 * Fintype.card K ^ (j + 1) = S.cc f (2 ^ j * u) (2 ^ j * u * (Tpol f (2 ^ j * u)).eval xa)
        (S.π xa) := by rw [S.cc_eq f j (by omega) u _ hu, h]; ring
    _ ≤ _ := S.cc_le_delta _ _ _ _

/-- **Lower bound** (`c₃ = 0 = w_α(a)`): the whole coset `x_a + 2^(k−j−2) R` solves. -/
theorem inter_lower_deep (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (j : ℕ)
    (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) (u : R) (hu : S.π u ≠ 0) (xa : R)
    (hw : S.π ((hasseDeriv 2 f).eval xa) + S.π (2 ^ (j - 1)) * S.π u *
      S.π ((hasseDeriv 3 f).eval xa) = 0)
    (hc : S.π ((hasseDeriv 3 f).eval xa) = 0) :
    Fintype.card K ^ (j + 2) ≤
      delta f (2 ^ j * u) (2 ^ j * u * (Tpol f (2 ^ j * u)).eval xa) := by
  set d := S.k - j - 2 with hd
  set Tp := Tpol f (2 ^ j * u) with hTp
  obtain ⟨g, hg, hπg⟩ := S.Tpol_deriv_spec f j hj u xa
  rw [hw] at hπg
  obtain ⟨g', hg'⟩ := (S.ker2 g).mp hπg
  have h2 : S.π ((hasseDeriv 2 Tp).eval xa) = 0 := by
    rw [hTp, S.Tpol_hasse2_spec f _ xa (S.pi_two_pow_mul j hj u), hc]
  obtain ⟨c2, hc2⟩ := (S.ker2 _).mp h2
  -- every x = xa + 2^d t solves
  have hsol : ∀ t, (2 : R) ^ (S.k - j) ∣ Tp.eval (xa + 2 ^ d * t) - Tp.eval xa := by
    intro t
    rw [eval_add_hasse Tp xa, Finset.sum_range_succ']
    simp only [hasseDeriv_zero, LinearMap.id_apply, pow_zero, mul_one, add_sub_cancel_right]
    apply Finset.dvd_sum
    intro i _
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · -- first derivative
        rw [zero_add, hasseDeriv_one, hg, hg']
        exact ⟨g' * t, by rw [show S.k - j = d + 2 by omega, pow_add]; ring⟩
      · -- second Hasse derivative
        rw [show 1 + 1 = 2 by rfl, hc2]
        have hle : S.k - j ≤ 2 * d + 1 := by omega
        refine ⟨2 ^ (2 * d + 1 - (S.k - j)) * c2 * t ^ 2, ?_⟩
        rw [mul_pow, ← pow_mul]
        have : (2 : R) ^ (2 * d + 1) = 2 ^ (S.k - j) * 2 ^ (2 * d + 1 - (S.k - j)) := by
          rw [← pow_add]; congr 1; omega
        calc 2 * c2 * (2 ^ (d * 2) * t ^ 2) = 2 ^ (2 * d + 1) * (c2 * t ^ 2) := by ring
          _ = _ := by rw [this]; ring
    · have hle : S.k - j ≤ d * (i + 1) := by
        have : d * 3 ≤ d * (i + 1) := Nat.mul_le_mul_left _ (by omega)
        omega
      refine ⟨(hasseDeriv (i + 1) Tp).eval xa * 2 ^ (d * (i + 1) - (S.k - j)) * t ^ (i + 1), ?_⟩
      rw [mul_pow, ← pow_mul]
      have : (2 : R) ^ (d * (i + 1)) = 2 ^ (S.k - j) * 2 ^ (d * (i + 1) - (S.k - j)) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring
  unfold delta
  rw [show j + 2 = S.k - d by omega, ← S.card_coset hcard d (by omega) xa]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_image, mem_I] at hx
  obtain ⟨y, ⟨t, rfl⟩, rfl⟩ := hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨w, hw'⟩ := hsol t
  exact (S.sol_iff f j (by omega) u _ _ hu).mpr ⟨w, hw'⟩

/-- **Lower bound** (`B_α(a) = 0`): both classes of the pair contribute. -/
theorem inter_lower_pair (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (j : ℕ) (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) (u : R) (hu : S.π u ≠ 0) (xa : R)
    (hc3 : ∀ a, (hasseDeriv 3 (f.map S.π)).eval a = 0)
    (hp2 : ∀ a, (hasseDeriv 2 (f.map S.π)).eval a ≠ 0)
    (hB : S.Afun f ρ (S.π xa) + S.π (2 ^ (j - 1)) * S.π u * μ = 0) :
    2 * Fintype.card K ^ (j + 1) ≤
      delta f (2 ^ j * u) (2 ^ j * u * (Tpol f (2 ^ j * u)).eval xa) := by
  obtain ⟨τ, hτ⟩ := S.surj ρ
  set γ := (Tpol f (2 ^ j * u)).eval xa with hγ
  have hw : ∀ x : R, S.π ((hasseDeriv 2 f).eval x) + S.π (2 ^ (j - 1)) * S.π u *
      S.π ((hasseDeriv 3 f).eval x) ≠ 0 := by
    intro x; rw [S.pi_hasse, S.pi_hasse, hc3, mul_zero, add_zero]; exact hp2 _
  have hroot : ∀ x c : R, (univ.filter (fun y : K => S.π c +
      (S.π ((hasseDeriv 2 f).eval x) + S.π (2 ^ (j - 1)) * S.π u * S.π ((hasseDeriv 3 f).eval x)) * y +
      S.π ((hasseDeriv 3 f).eval x) * y ^ 2 = 0)).card = 1 := by
    intro x c
    have h3 : S.π ((hasseDeriv 3 f).eval x) = 0 := by rw [S.pi_hasse]; exact hc3 _
    have := roots_lin (S.π ((hasseDeriv 2 f).eval x + 0)) (S.π c)
      (by rw [add_zero, S.pi_hasse]; exact hp2 _)
    rw [h3]
    simp only [mul_zero, add_zero, zero_mul] at this ⊢
    exact this
  -- class of xa
  have h1 := S.class_val hcard f j hj hjk u γ xa 0 (by ring) (hw xa)
  rw [hroot] at h1
  -- class of xa + τ
  obtain ⟨g, hg, hπg⟩ := S.Tpol_pair f ρ μ H j hj u xa τ hτ
  rw [hB] at hπg
  obtain ⟨g', hg'⟩ := (S.ker2 g).mp hπg
  have h2 := S.class_val hcard f j hj hjk u γ (xa + τ) g' (by rw [hγ, hg, hg']; ring) (hw _)
  rw [hroot] at h2
  have hne : S.π xa ≠ S.π (xa + τ) := by
    rw [map_add, hτ]; intro h; apply H.hρ; linear_combination -h
  calc 2 * Fintype.card K ^ (j + 1) =
      S.cc f (2 ^ j * u) (2 ^ j * u * γ) (S.π xa) + S.cc f (2 ^ j * u) (2 ^ j * u * γ) (S.π (xa + τ)) := by
        rw [S.cc_eq f j (by omega) u γ hu, S.cc_eq f j (by omega) u γ hu, h1, h2]; ring
    _ ≤ _ := S.two_cc_le_delta _ _ _ _ _ hne

/-- for a reduced residue polynomial with `p^[3] = c₃ ≠ 0`, `p^[2]` takes a value `≠ v` -/
theorem exists_hasse2_ne (p : K[X]) (hred : p.natDegree < Fintype.card K) (c3 : K)
    (hc3 : hasseDeriv 3 p = C c3) (hne : c3 ≠ 0) (h2 : (2 : K) = 0) (v : K) :
    ∃ a, (hasseDeriv 2 p).eval a ≠ v := by
  by_contra hall
  push Not at hall
  have hP : hasseDeriv 2 p - C v = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
    · intro a; simp [hall a]
    · calc (hasseDeriv 2 p - C v).natDegree ≤ max (hasseDeriv 2 p).natDegree (C v).natDegree :=
            natDegree_sub_le _ _
        _ ≤ p.natDegree := by
            rw [natDegree_C]
            exact max_le ((natDegree_hasseDeriv_le p 2).trans (Nat.sub_le _ _)) (Nat.zero_le _)
        _ < Fintype.card K := hred
  have h1 : hasseDeriv 1 (hasseDeriv 2 p) = 0 := by
    rw [sub_eq_zero.mp hP, hasseDeriv_C _ _ (by norm_num)]
  rw [hasse_hasse, hc3] at h1
  rw [← map_nsmul, C_eq_zero, nsmul_eq_mul] at h1
  have h1' := h1
  have h3 : (((1 + 2).choose 1 : ℕ) : K) = 1 := by norm_num; linear_combination h2
  rw [h3, one_mul] at h1'
  exact hne h1'

/-- **Theorem inter (iii)** for one direction `α = 2^j u` (`1 ≤ j ≤ k−3`):
all nonzero entries of the row equal `q^(j+1)` iff `c₃ = 0`, `p^[2]` has no zero and `B_α` has no zero. -/
theorem inter_flat_iff (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b →
      b = a ∨ b = a + ρ)
    (hred : (f.map S.π).natDegree < Fintype.card K) (c3 : K) (hc3 : hasseDeriv 3 (f.map S.π) = C c3)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) (u : R) (hu : S.π u ≠ 0) :
    (∀ β, delta f (2 ^ j * u) β = 0 ∨ delta f (2 ^ j * u) β = Fintype.card K ^ (j + 1)) ↔
      (c3 = 0 ∧ (∀ a, (hasseDeriv 2 (f.map S.π)).eval a ≠ 0) ∧
        ∀ a, S.Afun f ρ a + S.π (2 ^ (j - 1)) * S.π u * μ ≠ 0) := by
  have hq : 0 < Fintype.card K ^ (j + 1) := pow_pos Fintype.card_pos _
  have hq1 : 1 < Fintype.card K := by
    have : (0 : K) ≠ 1 := zero_ne_one
    exact Fintype.one_lt_card_iff.mpr ⟨0, 1, this⟩
  have hc3e : ∀ x : R, S.π ((hasseDeriv 3 f).eval x) = c3 := by
    intro x; rw [S.pi_hasse, hc3, eval_C]
  constructor
  · intro hflat
    have hbad : ∀ β, Fintype.card K ^ (j + 1) < delta f (2 ^ j * u) β → False := by
      intro β hlt
      rcases hflat β with h | h <;> omega
    by_cases h3 : c3 = 0
    · refine ⟨h3, ?_, ?_⟩
      · intro a ha
        obtain ⟨xa, rfl⟩ := S.surj a
        apply hbad _ (lt_of_lt_of_le _ (S.inter_lower_deep hcard f j hj hjk u hu xa
          (by rw [S.pi_hasse, ha, hc3e, h3, mul_zero, add_zero]) (by rw [hc3e, h3])))
        rw [pow_succ]
        exact lt_mul_of_one_lt_right hq hq1
      · intro a hB
        obtain ⟨xa, rfl⟩ := S.surj a
        have hc3' : ∀ a, (hasseDeriv 3 (f.map S.π)).eval a = 0 := by
          intro a; rw [hc3, eval_C, h3]
        have hp2 : ∀ a, (hasseDeriv 2 (f.map S.π)).eval a ≠ 0 := by
          intro a ha
          obtain ⟨xb, rfl⟩ := S.surj a
          apply hbad _ (lt_of_lt_of_le _ (S.inter_lower_deep hcard f j hj hjk u hu xb
            (by rw [S.pi_hasse, ha, hc3e, h3, mul_zero, add_zero]) (by rw [hc3e, h3])))
          rw [pow_succ]
          exact lt_mul_of_one_lt_right hq hq1
        apply hbad _ (lt_of_lt_of_le _ (S.inter_lower_pair hcard f ρ μ H j hj hjk u hu xa hc3' hp2 hB))
        omega
    · exfalso
      obtain ⟨a, ha⟩ := exists_hasse2_ne (f.map S.π) hred c3 hc3 h3 S.two_F
        (-(S.π (2 ^ (j - 1)) * S.π u * c3))
      obtain ⟨xa, rfl⟩ := S.surj a
      apply hbad _ (lt_of_lt_of_le _ (S.inter_lower_c3 hcard f j hj hjk u hu xa
        (by rw [S.pi_hasse, hc3e]; intro h; apply ha; linear_combination h) (by rw [hc3e]; exact h3)))
      omega
  · rintro ⟨h3, hp2, hB⟩ β
    have hc3' : ∀ a, (hasseDeriv 3 (f.map S.π)).eval a = 0 := by
      intro a; rw [hc3, eval_C, h3]
    have hup := (S.inter_upper hcard f ρ μ H hd2 j hj hjk u hu hc3' hp2 β).2 hB
    obtain ⟨m, hm⟩ := S.inter_dvd hcard f j hj (by omega) u β
    rw [hm] at hup ⊢
    have : m ≤ 1 := by
      by_contra hm1; push Not at hm1
      have := Nat.mul_lt_mul_of_pos_left hm1 hq
      omega
    interval_cases m <;> simp

end GRS

end APN2

#print axioms APN2.GRS.inter_lower_c3
#print axioms APN2.GRS.inter_lower_deep
#print axioms APN2.GRS.inter_lower_pair
#print axioms APN2.GRS.inter_flat_iff
