import Apn2R03.MainK3

/-!
# Middle and penultimate layers (Claude, 2026-10-25)

Extra hypothesis `hd2` : p'(a) = p'(b) ⇒ b ∈ {a, a+ρ}  ((H): p' = ε + K with ker K = {0, ρ}).
* `penultimate` (M4, k ≥ 4): for α = 2^(k-2) u (π u ≠ 0), the entry at β = f(x₀+α) − f(x₀) is
  q^(k-1) · (2 if A(π x₀) = 0 else 1); these are all nonzero entries.
* `middle_k3` (k = 3): for α = 2u, the entry at β = f(x₀+α) − f(x₀) is q² · (2 if ū A + ū² μ = 0 else 1).
* `O3_iff` : all these middle entries equal q² ⟺ (μ ≠ 0 ⇒ A ≡ 0) ∧ (μ = 0 ⇒ A has no zero).
* `tradeoff` : μ ≠ 0 and A ≡ 0 at k ≥ 4 force an exceptional entry ≥ q² and penultimate entries 2q^(k-1).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- `u w ∈ 4R` with `π u ≠ 0` forces `w ∈ 4R` -/
theorem four_dvd_of_unit_mul (u w : R) (hu : S.π u ≠ 0) (h : ∃ z, u * w = 4 * z) :
    ∃ z, w = 4 * z := by
  obtain ⟨z, hz⟩ := h
  have h1 : S.π w = 0 := by
    have := congrArg S.π hz
    rw [map_mul, map_mul, show (4 : R) = 2 * 2 by norm_num, map_mul, S.pi_two, zero_mul,
      zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hu
  obtain ⟨w1, rfl⟩ := (S.ker2 w).mp h1
  have h2 : 2 * (u * w1 - 2 * z) = 0 := by linear_combination hz
  obtain ⟨y, hy⟩ := S.tors _ h2
  have h3 : S.π (u * w1) = 0 := by
    have : u * w1 = 2 * z + 2 ^ (S.k - 1) * y := by linear_combination hy
    rw [this, map_add, S.pi_two_mul, S.pi_two_pow_mul _ (by have := S.hk; omega), add_zero]
  rw [map_mul] at h3
  obtain ⟨w2, rfl⟩ := (S.ker2 w1).mp ((mul_eq_zero.mp h3).resolve_left hu)
  exact ⟨w2, by ring⟩

theorem penult_value (hk4 : 4 ≤ S.k) (f : R[X]) (u x : R) :
    f.eval (x + 2 ^ (S.k - 2) * u) - f.eval x = 2 ^ (S.k - 2) * u * f.derivative.eval x := by
  obtain ⟨Q, hQ⟩ := taylor2 f x (2 ^ (S.k - 2) * u)
  have := S.two_pow_mul_sq_eq_zero (S.k - 2) (by omega) u
  rw [hQ, this]; ring

/-- f'(x) ≡ f'(x₀) (mod 4) exactly on the class of x₀ and, when A = 0, on the paired class -/
theorem deriv_mod4_iff (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b →
      b = a ∨ b = a + ρ) (x0 x : R) :
    (∃ z, f.derivative.eval x - f.derivative.eval x0 = 4 * z) ↔
      (S.π x = S.π x0 ∨ (S.π x = S.π x0 + ρ ∧ S.Afun f ρ (S.π x0) = 0)) := by
  constructor
  · rintro ⟨z, hz⟩
    have hπ : (f.map S.π).derivative.eval (S.π x0) = (f.map S.π).derivative.eval (S.π x) := by
      have := congrArg S.π hz
      rw [map_sub, S.pi_deriv_eval, S.pi_deriv_eval, show (4 : R) = 2 * 2 by norm_num,
        map_mul, map_mul, S.pi_two, zero_mul, zero_mul, sub_eq_zero] at this
      exact this.symm
    rcases hd2 _ _ hπ with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      obtain ⟨g, hg, hπg⟩ := S.A_spec f ρ H.hper x0 (x - x0) (S.π x0) rfl
        (by rw [map_sub, h]; ring)
      rw [← hπg]
      have e : x0 + (x - x0) = x := by ring
      rw [e, hz] at hg
      have := S.pi_eq_of_two_mul_eq (show 2 * g = 2 * (2 * z) by linear_combination -hg)
      rw [this, S.pi_two_mul]
  · rintro (h | ⟨h, hA⟩)
    · obtain ⟨y, hy⟩ := S.sub_two_of_pi_eq (y := x) (y' := x0) h
      obtain ⟨w, hw⟩ := dmod4 f x0 y
      refine ⟨w, ?_⟩
      have e : x = x0 + 2 * y := by linear_combination hy
      rw [e, hw]; ring
    · obtain ⟨g, hg, hπg⟩ := S.A_spec f ρ H.hper x0 (x - x0) (S.π x0) rfl
        (by rw [map_sub, h]; ring)
      rw [hA] at hπg
      obtain ⟨g', rfl⟩ := (S.ker2 g).mp hπg
      refine ⟨g', ?_⟩
      have e : x0 + (x - x0) = x := by ring
      rw [e] at hg
      rw [hg]; ring

/-- M4: penultimate rows -/
theorem penultimate (hcard : Fintype.card R = Fintype.card K ^ S.k) (hk4 : 4 ≤ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b →
      b = a ∨ b = a + ρ)
    (u x0 : R) (hu : S.π u ≠ 0) :
    delta f (2 ^ (S.k - 2) * u) (f.eval (x0 + 2 ^ (S.k - 2) * u) - f.eval x0) =
      Fintype.card K ^ (S.k - 1) * (if S.Afun f ρ (S.π x0) = 0 then 2 else 1) := by
  have hzero : ∀ w : R, 2 ^ (S.k - 2) * u * w = 0 ↔ ∃ z, w = 4 * z := by
    intro w
    constructor
    · intro h
      have h' : 2 ^ (S.k - 2) * (u * w) = 0 := by rw [← h]; ring
      obtain ⟨z, hz⟩ := S.ann_two_pow (S.k - 2) 2 (by omega) _ h'
      exact S.four_dvd_of_unit_mul u w hu ⟨z, by rw [hz]; norm_num⟩
    · rintro ⟨z, rfl⟩
      have : (2 : R) ^ (S.k - 2) * u * (4 * z) = 2 ^ S.k * (u * z) := by
        rw [show (4 : R) = 2 ^ 2 by norm_num,
          show (2 : R) ^ S.k = 2 ^ (S.k - 2) * 2 ^ 2 by rw [← pow_add]; congr 1; omega]
        ring
      rw [this, S.nil, zero_mul]
  have hset : univ.filter (fun x : R => f.eval (x + 2 ^ (S.k - 2) * u) - f.eval x =
      f.eval (x0 + 2 ^ (S.k - 2) * u) - f.eval x0) =
      univ.filter (fun x : R => S.π x = S.π x0 ∨
        (S.π x = S.π x0 + ρ ∧ S.Afun f ρ (S.π x0) = 0)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [S.penult_value hk4 f u x, S.penult_value hk4 f u x0, ← S.deriv_mod4_iff f ρ μ H hd2 x0 x]
    constructor
    · intro h
      exact (hzero _).mp (by rw [mul_sub, h, sub_self])
    · intro h
      have := (hzero _).mpr h
      rw [mul_sub, sub_eq_zero] at this
      exact this
  unfold delta
  rw [hset]
  have hne : S.π x0 ≠ S.π x0 + ρ := by intro h; apply H.hρ; linear_combination -h
  split_ifs with hA
  · have e : univ.filter (fun x : R => S.π x = S.π x0 ∨ (S.π x = S.π x0 + ρ ∧ S.Afun f ρ (S.π x0) = 0))
        = univ.filter (fun x : R => S.π x = S.π x0) ∪ univ.filter (fun x : R => S.π x = S.π x0 + ρ) := by
      ext x; simp [hA]
    have hdisj : Disjoint (univ.filter (fun x : R => S.π x = S.π x0))
        (univ.filter (fun x : R => S.π x = S.π x0 + ρ)) := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; exact hne (h1.symm.trans h2)
    rw [e, Finset.card_union_of_disjoint hdisj, S.card_fiber hcard, S.card_fiber hcard]; ring
  · have e : univ.filter (fun x : R => S.π x = S.π x0 ∨ (S.π x = S.π x0 + ρ ∧ S.Afun f ρ (S.π x0) = 0))
        = univ.filter (fun x : R => S.π x = S.π x0) := by
      ext x; simp [hA]
    rw [e, S.card_fiber hcard]; ring

/-- every penultimate entry is 0 or one of the values above -/
theorem penultimate_zero (_hk4 : 4 ≤ S.k) (f : R[X]) (u β : R)
    (h : ∀ x0, β ≠ f.eval (x0 + 2 ^ (S.k - 2) * u) - f.eval x0) :
    delta f (2 ^ (S.k - 2) * u) β = 0 := by
  unfold delta
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  exact h x hx.symm

/-- the middle layer at k = 3 -/
theorem middle_k3 (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b →
      b = a ∨ b = a + ρ)
    (u x0 : R) (hu : S.π u ≠ 0) :
    delta f (2 * u) (f.eval (x0 + 2 * u) - f.eval x0) = Fintype.card K ^ 2 *
      (if S.π u * S.Afun f ρ (S.π x0) + S.π u ^ 2 * μ = 0 then 2 else 1) := by
  have h8 : (8 : R) = 0 := by
    have := S.nil; rw [hk3] at this; norm_num at this; exact this
  have hval : ∀ x, f.eval (x + 2 * u) - f.eval x =
      2 * u * f.derivative.eval x + 4 * u ^ 2 * (hasseDeriv 2 f).eval x := by
    intro x
    obtain ⟨Q, hQ⟩ := taylor3 f x (2 * u)
    rw [hQ]; linear_combination (u ^ 3 * Q) * h8
  have hpair : ∀ x, S.π x = S.π x0 + ρ → ∃ g e : R,
      f.derivative.eval x - f.derivative.eval x0 = 2 * g ∧ S.π g = S.Afun f ρ (S.π x0) ∧
      S.π e = μ ∧ e = (hasseDeriv 2 f).eval x - (hasseDeriv 2 f).eval x0 := by
    intro x h
    obtain ⟨g, hg, hπg⟩ := S.A_spec f ρ H.hper x0 (x - x0) (S.π x0) rfl (by rw [map_sub, h]; ring)
    have e1 : x0 + (x - x0) = x := by ring
    rw [e1] at hg
    refine ⟨g, (hasseDeriv 2 f).eval x - (hasseDeriv 2 f).eval x0, hg, hπg, ?_, rfl⟩
    rw [map_sub, S.pi_hasse2_eval, S.pi_hasse2_eval, h, H.hμ]
  have hset : univ.filter (fun x : R => f.eval (x + 2 * u) - f.eval x =
      f.eval (x0 + 2 * u) - f.eval x0) =
      univ.filter (fun x : R => S.π x = S.π x0 ∨ (S.π x = S.π x0 + ρ ∧
        S.π u * S.Afun f ρ (S.π x0) + S.π u ^ 2 * μ = 0)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hval x, hval x0]
    constructor
    · intro h
      have h2 : 2 * (u * (f.derivative.eval x - f.derivative.eval x0) +
          2 * u ^ 2 * ((hasseDeriv 2 f).eval x - (hasseDeriv 2 f).eval x0)) = 0 := by
        linear_combination h
      obtain ⟨y, hy⟩ := S.tors _ h2
      rw [hk3] at hy
      have hD : S.π (u * (f.derivative.eval x - f.derivative.eval x0)) = 0 := by
        have e : u * (f.derivative.eval x - f.derivative.eval x0) =
            2 * (2 * y - u ^ 2 * ((hasseDeriv 2 f).eval x - (hasseDeriv 2 f).eval x0)) := by
          norm_num at hy; linear_combination hy
        rw [e, S.pi_two_mul]
      rw [map_mul, map_sub, S.pi_deriv_eval, S.pi_deriv_eval] at hD
      have hπ := sub_eq_zero.mp ((mul_eq_zero.mp hD).resolve_left hu)
      rcases hd2 _ _ hπ.symm with h1 | h1
      · exact Or.inl h1
      · refine Or.inr ⟨h1, ?_⟩
        obtain ⟨g, e, hg, hπg, hπe, he⟩ := hpair x h1
        have h4 : 4 * (u * g + u ^ 2 * e) = 0 := by rw [he]; linear_combination h - 2 * u * hg
        obtain ⟨w, hw⟩ := (S.four_mul_eq_zero_iff _).mp h4
        rw [hk3] at hw
        have := congrArg S.π hw
        rw [show (3 : ℕ) - 2 = 1 by norm_num, pow_one, S.pi_two_mul, map_add, map_mul, map_mul,
          map_pow, hπg, hπe] at this
        exact this
    · rintro (h1 | ⟨h1, hC⟩)
      · obtain ⟨y, hy⟩ := S.sub_two_of_pi_eq (y := x) (y' := x0) h1
        obtain ⟨w, hw⟩ := dmod4 f x0 y
        obtain ⟨v, hv⟩ := S.sub_two_of_pi_eq (y := (hasseDeriv 2 f).eval x)
          (y' := (hasseDeriv 2 f).eval x0) (by rw [S.pi_hasse2_eval, S.pi_hasse2_eval, h1])
        have ex : x = x0 + 2 * y := by linear_combination hy
        have hw' : f.derivative.eval x = f.derivative.eval x0 + 4 * w := by rw [ex, hw]
        linear_combination 2 * u * hw' + 4 * u ^ 2 * hv + (u * w + u ^ 2 * v) * h8
      · obtain ⟨g, e, hg, hπg, hπe, he⟩ := hpair x h1
        have hπ : S.π (u * g + u ^ 2 * e) = 0 := by
          rw [map_add, map_mul, map_mul, map_pow, hπg, hπe]; exact hC
        obtain ⟨w, hw⟩ := (S.ker2 _).mp hπ
        rw [he] at hw
        linear_combination 2 * u * hg + 4 * hw + w * h8
  unfold delta
  rw [hset]
  have hne : S.π x0 ≠ S.π x0 + ρ := by intro h; apply H.hρ; linear_combination -h
  have hq2 : Fintype.card K ^ (S.k - 1) = Fintype.card K ^ 2 := by rw [hk3]
  split_ifs with hC
  · have e : univ.filter (fun x : R => S.π x = S.π x0 ∨ (S.π x = S.π x0 + ρ ∧
          S.π u * S.Afun f ρ (S.π x0) + S.π u ^ 2 * μ = 0))
        = univ.filter (fun x : R => S.π x = S.π x0) ∪ univ.filter (fun x : R => S.π x = S.π x0 + ρ) := by
      ext x; simp [hC]
    have hdisj : Disjoint (univ.filter (fun x : R => S.π x = S.π x0))
        (univ.filter (fun x : R => S.π x = S.π x0 + ρ)) := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; exact hne (h1.symm.trans h2)
    rw [e, Finset.card_union_of_disjoint hdisj, S.card_fiber hcard, S.card_fiber hcard, hq2]; ring
  · have e : univ.filter (fun x : R => S.π x = S.π x0 ∨ (S.π x = S.π x0 + ρ ∧
          S.π u * S.Afun f ρ (S.π x0) + S.π u ^ 2 * μ = 0))
        = univ.filter (fun x : R => S.π x = S.π x0) := by
      ext x; simp [hC]
    rw [e, S.card_fiber hcard, hq2]; ring

/-- O3: all middle-layer entries (at the attained values) equal q² iff (O3) -/
theorem O3_iff (hk3 : S.k = 3) (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b →
      b = a ∨ b = a + ρ) :
    (∀ u x0 : R, S.π u ≠ 0 → delta f (2 * u) (f.eval (x0 + 2 * u) - f.eval x0) = Fintype.card K ^ 2) ↔
      ((μ ≠ 0 → ∀ a, S.Afun f ρ a = 0) ∧ (μ = 0 → ∀ a, S.Afun f ρ a ≠ 0)) := by
  have hq : 0 < Fintype.card K ^ 2 := pow_pos Fintype.card_pos 2
  have h2 := S.two_F
  constructor
  · intro hall
    refine ⟨fun hμ a => ?_, fun hμ a hA => ?_⟩
    · by_contra hA
      set t := S.Afun f ρ a / μ
      have ht : t ≠ 0 := div_ne_zero hA hμ
      have hval := S.middle_k3 hk3 hcard f ρ μ H hd2 (S.L t) (S.L a) (by rw [S.pi_L]; exact ht)
      rw [S.pi_L, S.pi_L, hall _ _ (by rw [S.pi_L]; exact ht)] at hval
      have hC : t * S.Afun f ρ a + t ^ 2 * μ = 0 := by
        simp only [t]; field_simp; linear_combination (S.Afun f ρ a) ^ 2 * h2
      rw [if_pos hC] at hval
      omega
    · have hval := S.middle_k3 hk3 hcard f ρ μ H hd2 (S.L 1) (S.L a) (by rw [S.pi_L]; exact one_ne_zero)
      rw [S.pi_L, S.pi_L, hall _ _ (by rw [S.pi_L]; exact one_ne_zero), hA, hμ] at hval
      rw [if_pos (by ring)] at hval
      omega
  · rintro ⟨h1, h0⟩ u x0 hu
    rw [S.middle_k3 hk3 hcard f ρ μ H hd2 u x0 hu]
    rw [if_neg]
    · ring
    · by_cases hμ : μ = 0
      · rw [hμ, mul_zero, add_zero]
        exact mul_ne_zero hu (h0 hμ _)
      · rw [h1 hμ, mul_zero, zero_add]
        exact mul_ne_zero (pow_ne_zero 2 hu) hμ

/-- M5: for μ ≠ 0, the k = 3 middle-layer optimum (A ≡ 0) is incompatible with k ≥ 4 exceptional
optimality: at every level k ≥ 4 such a lift has an exceptional entry ≥ q² and its penultimate entries are
2 q^(k-1). -/
theorem tradeoff (hcard : Fintype.card R = Fintype.card K ^ S.k) (hk4 : 4 ≤ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b →
      b = a ∨ b = a + ρ)
    (hA0 : ∀ a, S.Afun f ρ a = 0) (α : R) (hα : S.π α = ρ) :
    (∃ β, Fintype.card K ^ 2 ≤ delta f α β) ∧
      ∀ u x0 : R, S.π u ≠ 0 → delta f (2 ^ (S.k - 2) * u) (f.eval (x0 + 2 ^ (S.k - 2) * u) - f.eval x0)
        = 2 * Fintype.card K ^ (S.k - 1) := by
  refine ⟨S.lower_q2 hcard hk4 f ρ μ H α hα 0 (hA0 0), fun u x0 hu => ?_⟩
  rw [S.penultimate hcard hk4 f ρ μ H hd2 u x0 hu, if_pos (hA0 _)]; ring

end GRS

end APN2

#print axioms APN2.GRS.penultimate
#print axioms APN2.GRS.middle_k3
#print axioms APN2.GRS.O3_iff
#print axioms APN2.GRS.tradeoff
