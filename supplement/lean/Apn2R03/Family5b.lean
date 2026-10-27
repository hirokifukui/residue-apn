import Apn2R03.Family5a

/-!
# Theorem A for r ≥ 5 (Claude, 2026-10-25)

F = F5 (natural lift of P_{m,r}), F♯ = F + 2·X³, over an abstract Galois ring S : GRS R K,
|K| = 2^m, m odd, 5 ≤ r < m, r odd, gcd(r, m) = 1.
* (H) ⇒ Hyp with ρ = 1, μ = 0, Λ ≡ 0;
* A_F(a) = a^{2^{r-3}} + a^{2^{r-2}} + a^{2^{m-3}} + a^{2^{m-2}} (= L + L²), A_{F♯} = A_F + 1, Tr A_{F♯} = 1;
* every exceptional entry of F♯ is ≤ 2q; every lift of the same residue has an entry ≥ 2q;
* spectrum of F♯ on the exceptional direction: only 0 and 2q, with 2·n_{2q} = q^{k-1};
* the natural lift F is not optimal (some exceptional entry > 2q), since A_F(0) = 0.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

section ring
variable {T : Type*} [CommRing T]

theorem f5_derivT (h4 : (4 : T) = 0) (m r : ℕ) (hm : 4 ≤ m) (hr : 4 ≤ r) (x : T) :
    (F5 T m r).derivative.eval x = 1 + 2 * x + x ^ (2 ^ (r - 2)) + 2 * x * x ^ (2 ^ (r - 2))
      + x ^ (2 ^ (m - 2)) + 2 * x * x ^ (2 ^ (m - 2)) := by
  have hz : (Z5 T m r).derivative.eval x = 0 := by
    unfold Z5
    rw [derivative_sum, eval_finsetSum]
    apply sum_eq_zero
    intro i _
    simp only [derivative_add, eval_add, deriv_X_pow_evalT]
    push_cast
    rw [two_pow_q4 h4 (i + 2) (by omega), two_pow_q4 h4 (r - 2) (by omega),
      two_pow_q4 h4 (m - 2) (by omega)]
    ring
  unfold F5
  simp only [derivative_add, eval_add, deriv_X_pow_evalT, derivative_X, eval_one]
  rw [hz]
  have e1 : 2 ^ (r - 2) + 1 - 1 = 2 ^ (r - 2) := by generalize 2 ^ (r - 2) = w; omega
  have e2 : 2 ^ (r - 2) + 2 - 1 = 2 ^ (r - 2) + 1 := by generalize 2 ^ (r - 2) = w; omega
  have e3 : 2 ^ (m - 2) + 1 - 1 = 2 ^ (m - 2) := by generalize 2 ^ (m - 2) = w; omega
  have e4 : 2 ^ (m - 2) + 2 - 1 = 2 ^ (m - 2) + 1 := by generalize 2 ^ (m - 2) = w; omega
  rw [e1, e2, e3, e4]
  push_cast
  rw [two_pow_q4 h4 (r - 2) (by omega), two_pow_q4 h4 (m - 2) (by omega),
    two_pow_q4 h4 (m - 1) (by omega)]
  norm_num
  ring

theorem shiftW (h4 : (4 : T) = 0) (r : ℕ) (hr : 4 ≤ r) (x : T) :
    (x + 1) ^ (2 ^ (r - 2)) = x ^ (2 ^ (r - 2)) + 1 + 2 * x ^ (2 ^ (r - 3)) := by
  have := binom_mod4 h4 x (r - 3)
  rwa [show r - 3 + 1 = r - 2 by omega] at this

theorem f5_A_ring (h4 : (4 : T) = 0) (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) (x : T) :
    (F5 T m r).derivative.eval (x + 1) - (F5 T m r).derivative.eval x =
      2 * (x ^ (2 ^ (r - 3)) + x ^ (2 ^ (r - 2)) + x ^ (2 ^ (m - 3)) + x ^ (2 ^ (m - 2))) := by
  rw [f5_derivT h4 m r (by omega) (by omega), f5_derivT h4 m r (by omega) (by omega),
    shiftW h4 r (by omega), shiftU h4 m (by omega)]
  have := A_r5 h4 x (x ^ (2 ^ (m - 3))) (x ^ (2 ^ (m - 2))) (x ^ (2 ^ (r - 2))) (x ^ (2 ^ (r - 3)))
  linear_combination this

end ring

theorem f5_A_R {R : Type*} [CommRing R] (m r : ℕ) (hm : 5 ≤ m) (hr : 5 ≤ r) (x : R) : ∃ w : R,
    (F5 R m r).derivative.eval (x + 1) - (F5 R m r).derivative.eval x =
      2 * (x ^ (2 ^ (r - 3)) + x ^ (2 ^ (r - 2)) + x ^ (2 ^ (m - 3)) + x ^ (2 ^ (m - 2))) + 4 * w := by
  apply lift_Q4
  rw [map_sub, mk4_eval, mk4_eval, ← derivative_map, F5_map, map_add, map_one,
    f5_A_ring four_Q4 m r hm hr]
  simp only [map_mul, map_add, map_pow, map_ofNat]

section field
variable {K : Type*} [Field K] [CharP K 2]

def A5n (m r : ℕ) (a : K) : K :=
  a ^ (2 ^ (r - 3)) + a ^ (2 ^ (r - 2)) + a ^ (2 ^ (m - 3)) + a ^ (2 ^ (m - 2))

theorem A5s_trace [Fintype K] (m r : ℕ) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (a : K) :
    absTr m (1 + A5n m r a) = 1 := by
  unfold A5n
  rw [absTr_add, absTr_add, absTr_add, absTr_add, absTr_one m hodd,
    absTr_pow_two_pow m hcard a, absTr_pow_two_pow m hcard a, absTr_pow_two_pow m hcard a,
    absTr_pow_two_pow m hcard a]
  linear_combination (2 * absTr m a) * (two_K : (2 : K) = 0)

theorem A5s_ne [Fintype K] (m r : ℕ) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (a : K) :
    1 + A5n m r a ≠ 0 := by
  intro h
  have := A5s_trace m r hodd hcard a
  rw [h, absTr_zero] at this
  exact zero_ne_one this

end field

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem fam5_Lam (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hodd : Odd r) (a : K) :
    S.Lam (F5 R m r) 1 a = 0 := by
  haveI := S.charP2
  unfold Lam; rw [F5_map]; exact p5_Lam m r (by omega) hr5 hodd a

theorem fam5_hyp (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) :
    S.Hyp (F5 R m r) 1 0 ∧
      (∀ a b : K, ((F5 R m r).map S.π).derivative.eval a = ((F5 R m r).map S.π).derivative.eval b →
        b = a ∨ b = a + 1) := by
  haveI := S.charP2
  have h := S.hyp_of_H (F5 R m r) 1 (by rw [F5_map]; exact p5_quad m r hm5 hr5 hrm) one_ne_zero
    (by rw [F5_map]; exact p5_ker m r hm5 hr5 hrm hcard hcop)
    (by rw [F5_map]; exact p5_apn m r hm5 hr5 hrm hodd hcard hcop)
  have hμ : (hasseDeriv 2 ((F5 R m r).map S.π)).eval 1 - (hasseDeriv 2 ((F5 R m r).map S.π)).eval 0
      = 0 := by
    rw [F5_map, p5_hasse2 m r hm5 hr5, p5_hasse2 m r hm5 hr5, one_pow, one_pow,
      zero_pow (by positivity), zero_pow (by positivity)]
    linear_combination (1 : K) * (two_K : (2 : K) = 0)
  rw [hμ] at h
  exact h

theorem fam5_A (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (a : K) :
    S.Afun (F5 R m r) 1 a = A5n m r a := by
  haveI := S.charP2
  obtain ⟨g, hg, hπ⟩ := S.A_spec (F5 R m r) 1 (S.fam5_hyp m r hm5 hr5 hrm hodd hcard hcop).1.hper
    (S.L a) 1 a (S.pi_L a) (map_one _)
  obtain ⟨w, hw⟩ := f5_A_R m r hm5 hr5 (S.L a)
  rw [hw] at hg
  have h2 : S.π g = S.π ((S.L a ^ (2 ^ (r - 3)) + S.L a ^ (2 ^ (r - 2)) + S.L a ^ (2 ^ (m - 3))
      + S.L a ^ (2 ^ (m - 2))) + 2 * w) := S.pi_eq_of_two_mul_eq (by linear_combination -hg)
  rw [← hπ, h2, map_add, S.pi_two_mul, add_zero]
  simp only [map_add, map_pow, S.pi_L, A5n]

theorem fam5_sh_A (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) (a : K) :
    S.Afun (Fsh5 R m r) 1 a = 1 + A5n m r a := by
  haveI := S.charP2
  unfold Fsh5
  rw [S.A_control _ _ 1 (S.fam5_hyp m r hm5 hr5 hrm hodd hcard hcop).1.hper,
    S.fam5_A m r hm5 hr5 hrm hodd hcard hcop]
  have e : ∀ y : K, (((X : R[X]) ^ 3).derivative.map S.π).eval y = 3 * y ^ 2 := by
    intro y
    rw [← derivative_map, Polynomial.map_pow, map_X, deriv_X_pow_evalT]
    norm_num
  rw [e, e]
  linear_combination (3 * a + 1) * (two_K : (2 : K) = 0)

theorem fam5_sh_hyp (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r)
    (hcard : Fintype.card K = 2 ^ m) (hcop : Nat.Coprime r m) : S.Hyp (Fsh5 R m r) 1 0 :=
  S.hyp_add_two _ _ 1 0 (S.fam5_hyp m r hm5 hr5 hrm hodd hcard hcop).1

theorem fam5_sh_Lam (m r : ℕ) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hodd : Odd r) (a : K) :
    S.Lam (Fsh5 R m r) 1 a = 0 := by
  have := S.fam5_Lam (R := R) m r hm5 hr5 hodd a
  unfold Lam at this ⊢; unfold Fsh5; rw [S.map_add_two]; exact this

theorem fam5_sh_map (m r : ℕ) : (Fsh5 R m r).map S.π = F5 K m r := by
  unfold Fsh5; rw [S.map_add_two, F5_map]

/-- **Theorem A (r ≥ 5), upper bound.** -/
theorem fam5_upper (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (α β : R) (hα : S.π α = 1) :
    delta (Fsh5 R m r) α β ≤ 2 * Fintype.card K := by
  haveI := S.charP2
  have := S.upper_basic hcard (Fsh5 R m r) 1 0 (S.fam5_sh_hyp m r hm5 hr5 hrm hodd hm hcop)
    (fun a => by rw [S.fam5_sh_A m r hm5 hr5 hrm hodd hm hcop]; exact A5s_ne m r hmodd hm a) α β hα
  simpa using this

/-- **Theorem A (r ≥ 5), optimality over all lifts.** -/
theorem fam5_lower_all (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (g : R[X]) (hg : g.map S.π = F5 K m r) (α : R) (hα : S.π α = 1) :
    ∃ β, 2 * Fintype.card K ≤ delta g α β := by
  have hgm : g.map S.π = (F5 R m r).map S.π := by rw [hg, F5_map]
  have H := S.hyp_of_map_eq (F5 R m r) g hgm 1 0 (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).1
  have hL : S.Lam g 1 0 = 0 := by
    have := S.fam5_Lam (R := R) m r hm5 hr5 hodd 0
    unfold Lam at this ⊢; rw [hgm]; exact this
  exact S.lower_2q hcard g 1 0 H α hα 0 hL

/-- **Theorem A (r ≥ 5), spectrum.** -/
theorem fam5_spectrum (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hmodd : Odd m) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) (α : R) (hα : S.π α = 1) :
    2 * (univ.filter (fun β : R => delta (Fsh5 R m r) α β = 2 * Fintype.card K)).card =
        Fintype.card K ^ (S.k - 1) ∧
      (univ.filter (fun β : R => delta (Fsh5 R m r) α β = Fintype.card K)).card = 0 ∧
      ∀ β, delta (Fsh5 R m r) α β = 0 ∨ delta (Fsh5 R m r) α β = 2 * Fintype.card K := by
  haveI := S.charP2
  have hq : 0 < Fintype.card K := Fintype.card_pos
  obtain ⟨h1, h2, hall⟩ := S.spectrum_mu0 hcard (Fsh5 R m r) 1
    (S.fam5_sh_hyp m r hm5 hr5 hrm hodd hm hcop)
    (fun a => by rw [S.fam5_sh_A m r hm5 hr5 hrm hodd hm hcop]; exact A5s_ne m r hmodd hm a) α hα
  have hZ : (univ.filter (fun a : K => S.Lam (Fsh5 R m r) 1 a = 0)).card = Fintype.card K := by
    rw [filter_true_of_mem (fun a _ => S.fam5_sh_Lam m r hm5 hr5 hodd a), card_univ]
  rw [hZ] at h1 h2
  rw [Nat.sub_self, zero_mul] at h2
  have h2' := (Nat.mul_eq_zero.mp h2).resolve_left hq.ne'
  have h1' := Nat.eq_of_mul_eq_mul_left hq h1
  refine ⟨h1', h2', fun β => ?_⟩
  rcases hall β with h | h | h
  · exact Or.inl h
  · exfalso
    have : β ∈ univ.filter (fun β : R => delta (Fsh5 R m r) α β = Fintype.card K) := by simp [h]
    rw [card_eq_zero.mp h2'] at this
    exact absurd this (notMem_empty β)
  · exact Or.inr h

/-- **The natural lift (r ≥ 5) is not optimal**: some exceptional entry exceeds 2q. -/
theorem fam5_natural (hcard : Fintype.card R = Fintype.card K ^ S.k) (m r : ℕ) (hm5 : 5 ≤ m)
    (hr5 : 5 ≤ r) (hrm : r < m) (hodd : Odd r) (hm : Fintype.card K = 2 ^ m)
    (hcop : Nat.Coprime r m) :
    ∃ α β, S.π α = 1 ∧ 2 * Fintype.card K < delta (F5 R m r) α β := by
  haveI := S.charP2
  have H := (S.fam5_hyp m r hm5 hr5 hrm hodd hm hcop).1
  have hq : 2 < Fintype.card K := by
    rw [hm]; calc 2 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm5
  have hA0 : S.Afun (F5 R m r) 1 0 = 0 := by
    rw [S.fam5_A m r hm5 hr5 hrm hodd hm hcop]
    simp [A5n, zero_pow (show 2 ^ (r - 3) ≠ 0 by positivity),
      zero_pow (show 2 ^ (r - 2) ≠ 0 by positivity), zero_pow (show 2 ^ (m - 3) ≠ 0 by positivity),
      zero_pow (show 2 ^ (m - 2) ≠ 0 by positivity)]
  have hL0 := S.fam5_Lam (R := R) m r hm5 hr5 hodd 0
  by_contra hcon
  push Not at hcon
  rcases Nat.lt_or_ge S.k 4 with hk | hk
  · have hk3 : S.k = 3 := by have := S.hk; omega
    have hv : S.vmin3 (F5 R m r) 1 = 2 * Fintype.card K := by
      unfold vmin3; rw [if_neg]; push Not; exact ⟨0, hL0⟩
    have := (S.minimizers_k3 hk3 hcard m hm hq (F5 R m r) 1 0 H).mp
      (fun α β hα => by rw [hv]; exact hcon α β hα)
    exact this.1 rfl 0 hA0
  · have hv : S.vmin4 (F5 R m r) 1 0 = 2 * Fintype.card K := by
      unfold vmin4; rw [if_neg]; push Not; exact fun _ => ⟨0, hL0⟩
    have := (S.minimizers_k4 hcard hk m hm hq (F5 R m r) 1 0 H).mp
      (fun α β hα => by rw [hv]; exact hcon α β hα)
    exact this.1 0 hA0

end GRS

end APN2
