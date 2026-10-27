import Apn2R03.Family3c
import Apn2R03.Family5b

/-!
# Natural lifts of P_{m,r}: exact benchmarks (Claude, 2026-10-25, R05-07/09)

* `fam3_natural_exact` : r = 3, every level k ≥ 3: every exceptional row of the natural lift has
  maximum exactly 4q.
* `fam5_natural_q2`    : r ≥ 5, every level k ≥ 3: every exceptional row of the natural lift has an
  entry ≥ q² (the paper's Δ_exc ≥ q²; R04b only had > 2q).
* `A5n_zero`           : for r ≥ 5 the natural A_F vanishes only at 0 and 1.
* `fam5_nat_E0`        : E_F(0) = 1 + s for r = 2s + 1 (from F(2) − 2F(1) + F(0) = 10 − 6r mod 8).
* `fam5_nat_k3`        : at k = 3 every exceptional row of the natural lift has maximum exactly
  q² if r ≡ 1 (mod 4) and exactly 2q² if r ≡ 3 (mod 4).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

section Q8
variable {R : Type*} [CommRing R]

/-- the quotient ring R ⧸ (8) -/
abbrev Q8 (R : Type*) [CommRing R] := R ⧸ Ideal.span {(8 : R)}

theorem eight_Q8 : (8 : Q8 R) = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {(8 : R)}) (8 : R)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [← map_ofNat (Ideal.Quotient.mk (Ideal.span {(8 : R)})) 8]
  exact h

theorem lift_Q8 (a b : R) (h : (Ideal.Quotient.mk (Ideal.span {(8 : R)}) a) =
    Ideal.Quotient.mk (Ideal.span {(8 : R)}) b) : ∃ w, a = b + 8 * w := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by linear_combination hw⟩

theorem two_pow_q8 {T : Type*} [CommRing T] (h8 : (8 : T) = 0) (n : ℕ) (hn : 3 ≤ n) :
    (2 : T) ^ n = 0 := by
  rw [show n = 3 + (n - 3) by omega, pow_add, show (2 : T) ^ 3 = 8 by norm_num, h8, zero_mul]

end Q8

section evals
variable {T : Type*} [CommRing T]

theorem three_le_two_pow (n : ℕ) (hn : 2 ≤ n) : 3 ≤ 2 ^ n :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)

theorem Z5_eval_two (h8 : (8 : T) = 0) (m r : ℕ) (_hm : 4 ≤ m) (_hr : 4 ≤ r) :
    (Z5 T m r).eval 2 = 0 := by
  unfold Z5
  rw [eval_finsetSum]
  apply sum_eq_zero
  intro i _
  have hi := three_le_two_pow (i + 2) (by omega)
  simp only [eval_add, eval_pow, eval_X]
  rw [two_pow_q8 h8 _ hi, two_pow_q8 h8 (2 ^ (r - 2) + 2 ^ (i + 2)) (le_trans hi (Nat.le_add_left _ _)),
    two_pow_q8 h8 (2 ^ (m - 2) + 2 ^ (i + 2)) (le_trans hi (Nat.le_add_left _ _))]
  ring

theorem F5_eval_two_q8 (h8 : (8 : T) = 0) (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) :
    (F5 T m r).eval 2 = 6 := by
  have hw := three_le_two_pow (r - 2) (by omega)
  have hu := three_le_two_pow (m - 2) (by omega)
  have hv := three_le_two_pow (m - 1) (by omega)
  unfold F5
  simp only [eval_add, eval_pow, eval_X]
  rw [Z5_eval_two h8 m r (by omega) (by omega), two_pow_q8 h8 _ hw,
    two_pow_q8 h8 (2 ^ (r - 2) + 1) (by omega), two_pow_q8 h8 (2 ^ (r - 2) + 2) (by omega),
    two_pow_q8 h8 (2 ^ (r - 2) + 2 ^ (m - 2)) (by omega),
    two_pow_q8 h8 (2 ^ (r - 2) + 2 ^ (m - 1)) (by omega),
    two_pow_q8 h8 (2 ^ (m - 2) + 1) (by omega), two_pow_q8 h8 (2 ^ (m - 2) + 2) (by omega),
    two_pow_q8 h8 (2 ^ (m - 2) + 2 ^ (m - 1)) (by omega)]
  norm_num

theorem F5_eval_one (m r : ℕ) : (F5 T m r).eval 1 = 10 + 3 * ((r - 4 : ℕ) : T) := by
  unfold F5 Z5
  simp only [eval_add, eval_pow, eval_X, one_pow, eval_finsetSum, sum_const, card_range,
    nsmul_eq_mul]
  ring

theorem F5_eval_zero (m r : ℕ) (_hr : 4 ≤ r) : (F5 T m r).eval 0 = 0 := by
  unfold F5 Z5
  simp only [eval_add, eval_pow, eval_X, eval_finsetSum]
  have hp : ∀ n : ℕ, 1 ≤ n → (0 : T) ^ n = 0 := fun n hn => zero_pow (by omega)
  have e1 : 1 ≤ 2 ^ (r - 2) := Nat.one_le_two_pow
  have e2 : 1 ≤ 2 ^ (m - 2) := Nat.one_le_two_pow
  have e3 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  rw [sum_eq_zero (fun i _ => by
    rw [hp _ (Nat.one_le_two_pow), hp (2 ^ (r - 2) + 2 ^ (i + 2))
        (le_trans Nat.one_le_two_pow (Nat.le_add_left _ _)),
      hp (2 ^ (m - 2) + 2 ^ (i + 2)) (le_trans Nat.one_le_two_pow (Nat.le_add_left _ _))]; ring)]
  rw [hp 2 (by omega), hp _ (Nat.one_le_two_pow), hp (2 ^ (r - 2) + 1) (by omega),
    hp (2 ^ (r - 2) + 2) (by omega), hp (2 ^ (r - 2) + 2 ^ (m - 2)) (by omega),
    hp (2 ^ (r - 2) + 2 ^ (m - 1)) (by omega), hp (2 ^ (m - 2) + 1) (by omega),
    hp (2 ^ (m - 2) + 2) (by omega), hp (2 ^ (m - 2) + 2 ^ (m - 1)) (by omega)]
  ring

theorem F5_eval_two_R (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) : ∃ M : T, (F5 T m r).eval 2 = 6 + 8 * M := by
  apply lift_Q8
  have e : (Ideal.Quotient.mk (Ideal.span {(8 : T)})) ((F5 T m r).eval 2) =
      ((F5 T m r).map (Ideal.Quotient.mk (Ideal.span {(8 : T)}))).eval
        ((Ideal.Quotient.mk (Ideal.span {(8 : T)})) 2) := by
    rw [eval_map, eval₂_at_apply]
  rw [e, F5_map, map_ofNat, map_ofNat, F5_eval_two_q8 (eight_Q8 (R := T)) m r hm hr]

end evals

section field
variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

/-- **zeros of the natural A_F (r ≥ 5)**: A_F(a) = 0 only for a ∈ {0, 1} -/
theorem A5n_zero (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hmodd : Odd m)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (a : K) (h : A5n m r a = 0) :
    a = 0 ∨ a = 1 := by
  have h2 : (2 : K) = 0 := two_K
  set L := a ^ (2 ^ (r - 3)) + a ^ (2 ^ (m - 3)) with hLdef
  have hsq : L ^ 2 = a ^ (2 ^ (r - 2)) + a ^ (2 ^ (m - 2)) := by
    have e := frob_add 1 (a ^ (2 ^ (r - 3))) (a ^ (2 ^ (m - 3)))
    rw [pow_one] at e
    have sq2 : ∀ (x : K) (i : ℕ), (x ^ (2 ^ i)) ^ 2 = x ^ (2 ^ (i + 1)) := by
      intro x i; rw [← pow_mul, pow_succ]
    rw [hLdef, e, sq2, sq2, show r - 3 + 1 = r - 2 by omega,
      show m - 3 + 1 = m - 2 by omega]
  have hA : A5n m r a = L + L ^ 2 := by
    unfold A5n; rw [hsq, hLdef]; ring
  rw [hA] at h
  have hprod : L * (L + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hprod with hL | hL
  · -- L = 0: a^{2^{r-3}} = a^{2^{m-3}}, so a^{2^r} = a^{2^m} = a, so a ∈ F_2
    have heq : a ^ (2 ^ (r - 3)) = a ^ (2 ^ (m - 3)) := by
      linear_combination hL - (a ^ (2 ^ (m - 3))) * h2
    have hr' : a ^ (2 ^ r) = a ^ (2 ^ m) := by
      have e1 : a ^ (2 ^ r) = (a ^ (2 ^ (r - 3))) ^ (2 ^ 3) := by
        rw [← pow_mul, ← pow_add, show r - 3 + 3 = r by omega]
      have e2 : a ^ (2 ^ m) = (a ^ (2 ^ (m - 3))) ^ (2 ^ 3) := by
        rw [← pow_mul, ← pow_add, show m - 3 + 3 = m by omega]
      rw [e1, e2, heq]
    have hm' : a ^ (2 ^ m) = a := by rw [← hcard]; exact FiniteField.pow_card a
    have hg := frob_gcd a r m (by rw [hr', hm']) hm'
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
    have : a * (a - 1) = 0 := by linear_combination hg
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h1)
  · -- L = 1 is impossible: Tr L = 0 but Tr 1 = 1
    exfalso
    have hL1 : L = 1 := by linear_combination hL - h2
    have ht : absTr m L = 0 := by
      rw [hLdef, absTr_add, absTr_pow_two_pow m hcard, absTr_pow_two_pow m hcard]
      linear_combination (absTr m a) * h2
    rw [hL1, absTr_one m hmodd] at ht
    exact one_ne_zero ht

end field

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem cc_le_fiber (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (α β : R) (a : K) :
    S.cc f α β a ≤ Fintype.card K ^ (S.k - 1) := by
  rw [← S.card_fiber hcard a]
  unfold cc
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.1

/-- **r = 3: the natural lift has Δ_exc = 4q exactly, at every level k ≥ 3.** -/
theorem fam3_natural_exact (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ) (hm5 : 5 ≤ m)
    (hodd : Odd m) (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) (α : R) (hα : S.π α = 1) :
    (∀ β, delta (Fnat3 R m) α β ≤ 4 * Fintype.card K) ∧
      ∃ β, delta (Fnat3 R m) α β = 4 * Fintype.card K := by
  haveI := S.charP2
  have hup : ∀ β, delta (Fnat3 R m) α β ≤ 4 * Fintype.card K := by
    intro β
    have h := S.upper_basic hcard (Fnat3 R m) 1 1 (S.fam3_hyp m hm5 hm h3).1
      (fun a => by rw [S.fam3_A m hm5 hm h3]; exact A3_ne m hodd hm a) α β hα
    rw [if_neg one_ne_zero] at h
    calc delta (Fnat3 R m) α β ≤ 2 * Fintype.card K * 2 := h
      _ = 4 * Fintype.card K := by ring
  obtain ⟨β, hβ⟩ := S.fam3_natural hcard m hm5 hodd hm h3 α hα
  exact ⟨hup, β, le_antisymm (hup β) hβ⟩

theorem fam5_nat_A0 (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) : S.Afun (F5 R m r) 1 0 = 0 := by
  haveI := S.charP2
  rw [S.fam5_A m r hm5 hr5 hrm hodd hm hcop]
  simp [A5n, zero_pow (show 2 ^ (r - 3) ≠ 0 by positivity),
    zero_pow (show 2 ^ (r - 2) ≠ 0 by positivity), zero_pow (show 2 ^ (m - 3) ≠ 0 by positivity),
    zero_pow (show 2 ^ (m - 2) ≠ 0 by positivity)]

/-- class count at k = 3 for μ = 0 and A(a) = 0: q² if the gate constant is 0, else 0 -/
theorem cc_A0_mu0_k3 (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X])
    (ρ : K) (H : S.Hyp f ρ 0) (α β x c : R) (hα : S.π α = ρ) (hA : S.Afun f ρ (S.π x) = 0)
    (hc : (Gpoly f α β).eval x = 4 * c) :
    S.cc f α β (S.π x) = if S.π c = 0 then Fintype.card K ^ 2 else 0 := by
  rw [S.cc3_formula hk3 hcard f ρ 0 H α β x c hα hc, hA]
  split_ifs with h
  · rw [filter_true_of_mem (fun y _ => by rw [h]; ring), card_univ]; ring
  · rw [filter_false_of_mem (fun y _ => by
      intro h'; apply h; linear_combination h'), card_empty, mul_zero]

/-- **r ≥ 5: the natural lift has an exceptional entry ≥ q² in every exceptional row, at every
level k ≥ 3** (paper: Δ_exc ≥ q²). -/
theorem fam5_natural_q2 (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (α : R) (hα : S.π α = 1) :
    ∃ β, Fintype.card K ^ 2 ≤ delta (F5 R m r) α β := by
  haveI := S.charP2
  have H := (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).1
  have hA0 := S.fam5_nat_A0 m r hm5 hr5 hrm hodd hm hcop
  rcases Nat.lt_or_ge S.k 4 with hk | hk
  · have hk3 : S.k = 3 := by have := S.hk; omega
    refine ⟨(F5 R m r).eval (S.L 0 + α) - (F5 R m r).eval (S.L 0),
      le_trans ?_ (S.cc_le_delta _ α _ (S.π (S.L 0)))⟩
    have h0 : (Gpoly (F5 R m r) α ((F5 R m r).eval (S.L 0 + α) - (F5 R m r).eval (S.L 0))).eval
        (S.L 0) = 4 * 0 := by rw [Gpoly_eval]; ring
    rw [S.cc_A0_mu0_k3 hk3 hcard _ 1 H α _ (S.L 0) 0 hα (by rw [S.pi_L]; exact hA0) h0,
      if_pos (map_zero _)]
  · exact S.lower_q2 hcard hk (F5 R m r) 1 0 H α hα 0 hA0

/-- **E_F(0) for the natural lift (r ≥ 5)**: with r = 2s + 1, E_F(0) = 1 + s.
It comes from F(2) − 2F(1) + F(0) = 6 − 2(3r − 2) = 10 − 6r modulo 8. -/
theorem fam5_nat_E0 (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (s : ℕ) (hs : r = 2 * s + 1) :
    S.Efun (F5 R m r) 1 0 = 1 + (s : K) := by
  haveI := S.charP2
  have h2 : (2 : K) = 0 := two_K
  have H := (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).1
  obtain ⟨c, hc, hπc⟩ := S.E_spec (F5 R m r) 1 H.hper 0 1 0 (map_zero _) (map_one _)
    (S.fam5_Lam (R := R) m r hm5 hr5 hodd 0)
  obtain ⟨M, hM⟩ := F5_eval_two_R (T := R) m r hm5 hr5
  have h1 := F5_eval_one (T := R) m r
  have h0 := F5_eval_zero (T := R) m r (by omega)
  have hr4 : ((r - 4 : ℕ) : R) = 2 * (s : R) - 3 := by
    rw [Nat.cast_sub (by omega), hs]; push_cast; ring
  unfold Sx at hc
  rw [show (0 : R) + 2 * 1 = 2 by ring, zero_add, h0, hM, h1, hr4] at hc
  have key : 4 * c = 4 * (1 + 2 * M - 3 * (s : R)) := by rw [← hc]; ring
  have hπ := S.pi_eq_of_four_mul_eq key
  rw [← hπc, hπ]
  simp only [map_add, map_sub, map_mul, map_one, map_natCast, map_ofNat]
  rw [h2]
  linear_combination (-2 * (s : K)) * h2

/-- **The natural lift (r ≥ 5) at k = 3**: every exceptional row has maximum exactly q² when
r ≡ 1 (mod 4), and exactly 2q² when r ≡ 3 (mod 4). -/
theorem fam5_nat_k3 (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ)
    (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m)
    (hm : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (α : R) (hα : S.π α = 1) :
    (r % 4 = 1 → (∀ β, delta (F5 R m r) α β ≤ Fintype.card K ^ 2) ∧
        ∃ β, delta (F5 R m r) α β = Fintype.card K ^ 2) ∧
      (r % 4 = 3 → (∀ β, delta (F5 R m r) α β ≤ 2 * Fintype.card K ^ 2) ∧
        ∃ β, delta (F5 R m r) α β = 2 * Fintype.card K ^ 2) := by
  haveI := S.charP2
  have h2 : (2 : K) = 0 := two_K
  have H := (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).1
  have hA0 := S.fam5_nat_A0 m r hm5 hr5 hrm hodd hm hcop
  have hq2 : 2 ≤ Fintype.card K := by
    rw [hm]; calc 2 ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfib : ∀ (β : R) (a : K), S.cc (F5 R m r) α β a ≤ Fintype.card K ^ 2 := by
    intro β a; have := S.cc_le_fiber hcard (F5 R m r) α β a; rwa [hk3] at this
  obtain ⟨s, hs⟩ : ∃ s, r = 2 * s + 1 := ⟨r / 2, by obtain ⟨t, ht⟩ := hodd; omega⟩
  have hE0 := S.fam5_nat_E0 m r hm5 hr5 hrm hodd hm hcop s hs
  -- E(1) = E(0)
  have hE1 : S.Efun (F5 R m r) 1 1 = S.Efun (F5 R m r) 1 0 := by
    have := S.E_transl (F5 R m r) 1 0 H.hper H.hμ 0 (S.fam5_Lam (R := R) m r hm5 hr5 hodd 0)
    rw [zero_add, hA0] at this
    linear_combination this - (S.Efun (F5 R m r) 1 0) * h2
  have hA1 : S.Afun (F5 R m r) 1 1 = 0 := by
    have := S.A_periodic (F5 R m r) 1 H.hper 0; rw [zero_add] at this; rw [this, hA0]
  constructor
  · intro hr1
    have hsE : (s : K) = 0 := by
      rw [CharP.cast_eq_zero_iff K 2]; omega
    refine ⟨fun β => ?_, ?_⟩
    · rcases S.delta_pair' (F5 R m r) 1 0 H α β hα with h | ⟨a0, h⟩
      · rw [h]; exact Nat.zero_le _
      · rw [h]
        have hxb : S.π (S.L a0 + α) = a0 + 1 := by rw [map_add, S.pi_L, hα]
        by_cases hA : S.Afun (F5 R m r) 1 a0 = 0
        · -- a0 ∈ {0, 1}; at most one class of the pair contributes
          have hA' := hA
          rw [S.fam5_A m r hm5 hr5 hrm hodd hm hcop] at hA'
          have ha01 := A5n_zero m r hm5 hr5 hmodd hm hcop a0 hA'
          have hEa : S.Efun (F5 R m r) 1 a0 = 1 := by
            rcases ha01 with rfl | rfl
            · rw [hE0, hsE, add_zero]
            · rw [hE1, hE0, hsE, add_zero]
          by_contra hgt
          push Not at hgt
          have hne1 : S.cc (F5 R m r) α β (S.π (S.L a0)) ≠ 0 := by
            intro h0; rw [h0, zero_add] at hgt; exact absurd (hfib β _) (not_le.mpr hgt)
          have hne2 : S.cc (F5 R m r) α β (S.π (S.L a0 + α)) ≠ 0 := by
            intro h0; rw [h0, add_zero] at hgt; exact absurd (hfib β _) (not_le.mpr hgt)
          have hg1 : ∃ c, (Gpoly (F5 R m r) α β).eval (S.L a0) = 4 * c := by
            by_contra hn; exact hne1 (S.cc_zero _ 1 H.hper α β _ hα hn)
          have hg2 : ∃ c, (Gpoly (F5 R m r) α β).eval (S.L a0 + α) = 4 * c := by
            by_contra hn; exact hne2 (S.cc_zero _ 1 H.hper α β _ hα hn)
          obtain ⟨c, hc⟩ := hg1
          obtain ⟨c', hc'⟩ := hg2
          have hpair := (S.gate_pair_zero (F5 R m r) 1 0 H α β hα a0
            (S.fam5_Lam (R := R) m r hm5 hr5 hodd a0)).2 c c' hc hc'
          rw [S.cc_A0_mu0_k3 hk3 hcard _ 1 H α β _ c hα (by rw [S.pi_L]; exact hA) hc] at hne1
          rw [S.cc_A0_mu0_k3 hk3 hcard _ 1 H α β _ c' hα
            (by rw [hxb, S.A_periodic (F5 R m r) 1 H.hper]; exact hA) hc'] at hne2
          have hz1 : S.π c = 0 := by by_contra hn; rw [if_neg hn] at hne1; exact hne1 rfl
          have hz2 : S.π c' = 0 := by by_contra hn; rw [if_neg hn] at hne2; exact hne2 rfl
          rw [hz1, hz2, hEa, zero_add] at hpair
          exact zero_ne_one hpair
        · have hAb : S.Afun (F5 R m r) 1 (S.π (S.L a0 + α)) ≠ 0 := by
            rw [hxb, S.A_periodic (F5 R m r) 1 H.hper]; exact hA
          have c1 := S.cc_le hcard (F5 R m r) 1 0 H α β hα (S.L a0) (by rw [S.pi_L]; exact hA)
          have c2 := S.cc_le hcard (F5 R m r) 1 0 H α β hα (S.L a0 + α) hAb
          rw [if_pos rfl] at c1 c2
          nlinarith
    · obtain ⟨β, hβ⟩ := S.fam5_natural_q2 hcard m r hm5 hr5 hrm hodd hm hcop α hα
      refine ⟨β, le_antisymm ?_ hβ⟩
      -- reuse the upper bound proved above
      rcases S.delta_pair' (F5 R m r) 1 0 H α β hα with h | ⟨a0, h⟩
      · rw [h]; exact Nat.zero_le _
      · rw [h]
        have hxb : S.π (S.L a0 + α) = a0 + 1 := by rw [map_add, S.pi_L, hα]
        by_cases hA : S.Afun (F5 R m r) 1 a0 = 0
        · have hA' := hA
          rw [S.fam5_A m r hm5 hr5 hrm hodd hm hcop] at hA'
          have ha01 := A5n_zero m r hm5 hr5 hmodd hm hcop a0 hA'
          have hEa : S.Efun (F5 R m r) 1 a0 = 1 := by
            rcases ha01 with rfl | rfl
            · rw [hE0, hsE, add_zero]
            · rw [hE1, hE0, hsE, add_zero]
          by_contra hgt
          push Not at hgt
          have hne1 : S.cc (F5 R m r) α β (S.π (S.L a0)) ≠ 0 := by
            intro h0; rw [h0, zero_add] at hgt; exact absurd (hfib β _) (not_le.mpr hgt)
          have hne2 : S.cc (F5 R m r) α β (S.π (S.L a0 + α)) ≠ 0 := by
            intro h0; rw [h0, add_zero] at hgt; exact absurd (hfib β _) (not_le.mpr hgt)
          have hg1 : ∃ c, (Gpoly (F5 R m r) α β).eval (S.L a0) = 4 * c := by
            by_contra hn; exact hne1 (S.cc_zero _ 1 H.hper α β _ hα hn)
          have hg2 : ∃ c, (Gpoly (F5 R m r) α β).eval (S.L a0 + α) = 4 * c := by
            by_contra hn; exact hne2 (S.cc_zero _ 1 H.hper α β _ hα hn)
          obtain ⟨c, hc⟩ := hg1
          obtain ⟨c', hc'⟩ := hg2
          have hpair := (S.gate_pair_zero (F5 R m r) 1 0 H α β hα a0
            (S.fam5_Lam (R := R) m r hm5 hr5 hodd a0)).2 c c' hc hc'
          rw [S.cc_A0_mu0_k3 hk3 hcard _ 1 H α β _ c hα (by rw [S.pi_L]; exact hA) hc] at hne1
          rw [S.cc_A0_mu0_k3 hk3 hcard _ 1 H α β _ c' hα
            (by rw [hxb, S.A_periodic (F5 R m r) 1 H.hper]; exact hA) hc'] at hne2
          have hz1 : S.π c = 0 := by by_contra hn; rw [if_neg hn] at hne1; exact hne1 rfl
          have hz2 : S.π c' = 0 := by by_contra hn; rw [if_neg hn] at hne2; exact hne2 rfl
          rw [hz1, hz2, hEa, zero_add] at hpair
          exact zero_ne_one hpair
        · have hAb : S.Afun (F5 R m r) 1 (S.π (S.L a0 + α)) ≠ 0 := by
            rw [hxb, S.A_periodic (F5 R m r) 1 H.hper]; exact hA
          have c1 := S.cc_le hcard (F5 R m r) 1 0 H α β hα (S.L a0) (by rw [S.pi_L]; exact hA)
          have c2 := S.cc_le hcard (F5 R m r) 1 0 H α β hα (S.L a0 + α) hAb
          rw [if_pos rfl] at c1 c2
          nlinarith
  · intro hr3
    have hsE : (s : K) = 1 := by
      obtain ⟨t, ht⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      rw [ht]; push_cast; rw [h2]; ring
    refine ⟨fun β => ?_, ?_⟩
    · rcases S.delta_pair' (F5 R m r) 1 0 H α β hα with h | ⟨a0, h⟩
      · rw [h]; exact Nat.zero_le _
      · rw [h]; have := hfib β (S.π (S.L a0)); have := hfib β (S.π (S.L a0 + α)); omega
    · set β := (F5 R m r).eval (S.L 0 + α) - (F5 R m r).eval (S.L 0) with hβdef
      have h0 : (Gpoly (F5 R m r) α β).eval (S.L 0) = 4 * 0 := by rw [Gpoly_eval, hβdef]; ring
      have hcc0 := S.cc_A0_mu0_k3 hk3 hcard _ 1 H α β (S.L 0) 0 hα (by rw [S.pi_L]; exact hA0) h0
      rw [if_pos (map_zero _), S.pi_L] at hcc0
      obtain ⟨c', hc', hπc'⟩ := S.cc_shift (F5 R m r) 1 H.hper α β (S.L 0) 0 hα
        (by rw [S.pi_L]; exact S.fam5_Lam (R := R) m r hm5 hr5 hodd 0) h0
      rw [S.pi_L, map_zero, zero_add, hE0, hsE] at hπc'
      have hπc'0 : S.π c' = 0 := by rw [hπc']; linear_combination h2
      have hxb : S.π (S.L 0 + α) = 0 + 1 := by rw [map_add, S.pi_L, hα]
      have hcc1 := S.cc_A0_mu0_k3 hk3 hcard _ 1 H α β (S.L 0 + α) c' hα
        (by rw [hxb, S.A_periodic (F5 R m r) 1 H.hper]; exact hA0) hc'
      rw [if_pos hπc'0, hxb] at hcc1
      have hq0 : 0 < Fintype.card K := Fintype.card_pos
      have hd := S.delta_at (F5 R m r) 1 0 H α β hα 0 (by rw [hcc0]; positivity)
      refine ⟨β, ?_⟩
      rw [hd, hcc0, hcc1]; ring

end GRS

end APN2

#print axioms APN2.A5n_zero
#print axioms APN2.GRS.fam3_natural_exact
#print axioms APN2.GRS.fam5_natural_q2
#print axioms APN2.GRS.fam5_nat_E0
#print axioms APN2.GRS.fam5_nat_k3
