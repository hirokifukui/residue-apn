import Apn2R03.Inter2
import Apn2R03.Bounds

/-!
# Intermediate layers, part 3: class counts and the upper bound (Claude, 2026-10-26, R05c)

`α = 2^j u`, `π u ≠ 0`, `1 ≤ j`, `j + 3 ≤ k`, `T = Tpol f α` (`α T(x) = F(x+α) − F(x)`).
* `sol_iff`         : `F(x+α) − F(x) = α γ ↔ T(x) − γ ∈ 2^(k−j) R`;
* `Tpol_pair`       : `T(x+τ) − T(x) = 2 g` with `π g = A_F(π x) + π(2^(j−1)) ū μ` (`π τ = ρ`);
* `class_count_gen` : the local count of `G ∈ 2^e R` on one residue class (simple root);
* `class_val`       : one class contributes `q^(j+1) · #{y : c̄ + w̄ y + c̄₃ y² = 0}`;
* `inter_upper`     : Theorem inter (ii) as bounds: if `c₃ = 0` and `p^[2]` has no zero, every entry is
                      `≤ 2 q^(j+1)`, and `≤ q^(j+1)` when `B_α = A_F + π(2^(j−1)) ū μ` has no zero.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

theorem pi_two_pow_pred (j : ℕ) (hj : 1 ≤ j) :
    S.π ((2 : R) ^ (j - 1)) = if j = 1 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · rw [← mul_one ((2 : R) ^ (j - 1)), S.pi_two_pow_mul _ (by omega)]

/-- `F(x+α) − F(x) = α γ` iff `T(x) ≡ γ (mod 2^(k−j))` -/
theorem sol_iff (f : R[X]) (j : ℕ) (hjk : j ≤ S.k) (u γ x : R) (hu : S.π u ≠ 0) :
    f.eval (x + 2 ^ j * u) - f.eval x = 2 ^ j * u * γ ↔
      ∃ w, (Tpol f (2 ^ j * u)).eval x - γ = 2 ^ (S.k - j) * w := by
  rw [← Tpol_eval_mul]
  constructor
  · intro h
    apply S.unit_ann j hjk u _ hu
    linear_combination h
  · rintro ⟨w, hw⟩
    have e : (2 : R) ^ j * 2 ^ (S.k - j) = 2 ^ S.k := by rw [← pow_add]; congr 1; omega
    have : 2 ^ j * u * ((Tpol f (2 ^ j * u)).eval x - γ) = 0 := by
      rw [hw, show (2 : R) ^ j * u * (2 ^ (S.k - j) * w) = 2 ^ j * 2 ^ (S.k - j) * (u * w) by ring, e,
        S.nil, zero_mul]
    linear_combination this

/-- `T(x+τ) − T(x)` modulo 4, `π τ = ρ` -/
theorem Tpol_pair (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (j : ℕ) (hj : 1 ≤ j) (u x τ : R)
    (hτ : S.π τ = ρ) :
    ∃ g, (Tpol f (2 ^ j * u)).eval (x + τ) - (Tpol f (2 ^ j * u)).eval x = 2 * g ∧
      S.π g = S.Afun f ρ (S.π x) + S.π (2 ^ (j - 1)) * S.π u * μ := by
  obtain ⟨s1, hs1⟩ := Tpol_split f (2 ^ j * u) (x + τ)
  obtain ⟨s0, hs0⟩ := Tpol_split f (2 ^ j * u) x
  obtain ⟨gA, hgA, hπA⟩ := S.A_spec f ρ H.hper x τ (S.π x) rfl hτ
  have e1 : (2 : R) ^ j = 2 * 2 ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
  have e2 : ((2 : R) ^ j * u) ^ 2 = 2 * (2 ^ (2 * j - 1) * u ^ 2) := by
    rw [mul_pow, ← pow_mul, show j * 2 = (2 * j - 1) + 1 by omega, pow_succ]; ring
  refine ⟨gA + 2 ^ (j - 1) * u * ((hasseDeriv 2 f).eval (x + τ) - (hasseDeriv 2 f).eval x) +
      2 ^ (2 * j - 1) * u ^ 2 * (s1 - s0), ?_, ?_⟩
  · rw [hs1, hs0, e2]
    have : f.derivative.eval (x + τ) = f.derivative.eval x + 2 * gA := by linear_combination hgA
    rw [this, e1]; ring
  · have hμ' : S.π ((hasseDeriv 2 f).eval (x + τ) - (hasseDeriv 2 f).eval x) = μ := by
      rw [map_sub, S.pi_hasse, S.pi_hasse, map_add, hτ]; exact H.hμ (S.π x)
    have hpow : S.π ((2 : R) ^ (2 * j - 1)) = 0 := by
      rw [← mul_one ((2 : R) ^ (2 * j - 1)), S.pi_two_pow_mul _ (by omega)]
    rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul, hμ', hpow, hπA]; ring

section card
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- the local count of `G(x) ∈ 2^e R` on the class of `x_a` (simple-root case) -/
theorem class_count_gen (hcard : Fintype.card R = Fintype.card K ^ S.k) (G : R[X]) (xa c g : R)
    (hc : G.eval xa = 4 * c) (hg : G.derivative.eval xa = 2 * g) (hgπ : S.π g ≠ 0)
    (e : ℕ) (he : 3 ≤ e) (hek : e ≤ S.k) :
    (univ.filter (fun x : R => S.π x = S.π xa ∧ ∃ w, G.eval x = 2 ^ e * w)).card =
      Fintype.card K ^ (S.k - e + 1) * (univ.filter (fun y : K =>
        S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card := by
  obtain ⟨P, hP4, hPbar⟩ := S.exists_local_poly G xa c g hc hg
  have hsimple : ∀ t : K, (P.map S.π).eval t = 0 → (P.map S.π).derivative.eval t ≠ 0 := by
    intro t _; rw [(hPbar t).2]; exact hgπ
  have hk := S.hk
  have hTcard := S.card_T hcard P hsimple (e - 2) (by omega) (by omega)
  have hroots : univ.filter (fun t : K => (P.map S.π).eval t = 0) =
      univ.filter (fun y : K =>
        S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, (hPbar y).1]
  rw [hroots, show S.k - (e - 2) = S.k - e + 2 by omega] at hTcard
  have e4 : (2 : R) ^ e = 4 * 2 ^ (e - 2) := by
    rw [show (4 : R) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hT : ∀ z, z ∈ T P (e - 2) ↔ ∃ w, G.eval (xa + 2 * z) = 2 ^ e * w := by
    intro z
    rw [mem_T]
    constructor
    · rintro ⟨w, hw⟩; exact ⟨w, by rw [← hP4, hw, e4]; ring⟩
    · rintro ⟨w, hw⟩
      have h0 : 4 * (P.eval z - 2 ^ (e - 2) * w) = 0 := by
        rw [mul_sub, hP4, hw, e4]; ring
      obtain ⟨v, hv⟩ := (S.four_mul_eq_zero_iff _).mp h0
      refine ⟨w + 2 ^ (S.k - e) * v, ?_⟩
      have e2 : (2 : R) ^ (S.k - 2) = 2 ^ (e - 2) * 2 ^ (S.k - e) := by
        rw [← pow_add]; congr 1; omega
      linear_combination hv + 0 * e2 + v * e2
  set C0 := univ.filter (fun x : R => S.π x = S.π xa ∧ ∃ w, G.eval x = 2 ^ e * w) with hC0
  have key := Finset.card_eq_sum_card_fiberwise (s := T P (e - 2)) (t := C0)
    (f := fun z => xa + 2 * z) (fun z hz => by
      rw [Finset.mem_coe, hC0, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, (hT z).mp hz⟩
      rw [map_add, S.pi_two_mul, add_zero])
  have hfib : ∀ x ∈ C0, ((T P (e - 2)).filter (fun z => xa + 2 * z = x)).card = Fintype.card K := by
    intro x hx
    rw [hC0, Finset.mem_filter] at hx
    obtain ⟨-, hxa, hGx⟩ := hx
    have : S.π (x - xa) = 0 := by rw [map_sub, hxa, sub_self]
    obtain ⟨y0, hy0⟩ := (S.ker2 _).mp this
    rw [← S.card_ann_two hcard]
    apply Finset.card_bij (fun z _ => z - y0)
    · intro z hz
      rw [Finset.mem_filter] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hz.2
      linear_combination this + hy0
    · intro z _ w _ h; simpa using h
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨w + y0, ?_, by ring⟩
      rw [Finset.mem_filter, hT]
      constructor
      · have : xa + 2 * (w + y0) = x := by linear_combination hw - hy0
        rw [this]; exact hGx
      · linear_combination hw - hy0
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hTcard] at key
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have : (univ.filter (fun y : K =>
      S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card *
      Fintype.card K ^ (S.k - e + 2) = (Fintype.card K ^ (S.k - e + 1) * (univ.filter (fun y : K =>
      S.π c + S.π g * y + S.π ((hasseDeriv 2 G).eval xa) * y ^ 2 = 0)).card) * Fintype.card K := by
    ring
  rw [this] at key
  exact (Nat.eq_of_mul_eq_mul_right hq key).symm

/-- the contribution of one class to the row of `α = 2^j u` -/
theorem class_val (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (j : ℕ) (hj : 1 ≤ j)
    (hjk : j + 3 ≤ S.k) (u γ xa c : R)
    (hc : (Tpol f (2 ^ j * u)).eval xa - γ = 4 * c)
    (hw : S.π ((hasseDeriv 2 f).eval xa) + S.π (2 ^ (j - 1)) * S.π u * S.π ((hasseDeriv 3 f).eval xa) ≠ 0) :
    (univ.filter (fun x : R => S.π x = S.π xa ∧
        ∃ w, (Tpol f (2 ^ j * u)).eval x - γ = 2 ^ (S.k - j) * w)).card =
      Fintype.card K ^ (j + 1) * (univ.filter (fun y : K => S.π c +
        (S.π ((hasseDeriv 2 f).eval xa) + S.π (2 ^ (j - 1)) * S.π u * S.π ((hasseDeriv 3 f).eval xa)) * y +
        S.π ((hasseDeriv 3 f).eval xa) * y ^ 2 = 0)).card := by
  obtain ⟨g, hg, hπg⟩ := S.Tpol_deriv_spec f j hj u xa
  set G : R[X] := Tpol f (2 ^ j * u) - C γ with hG
  have hGe : ∀ x, G.eval x = (Tpol f (2 ^ j * u)).eval x - γ := by intro x; simp [G]
  have hGd : G.derivative.eval xa = 2 * g := by simp [G, hg]
  have hG2 : S.π ((hasseDeriv 2 G).eval xa) = S.π ((hasseDeriv 3 f).eval xa) := by
    have : hasseDeriv 2 G = hasseDeriv 2 (Tpol f (2 ^ j * u)) := by
      simp only [G, map_sub, hasseDeriv_C _ _ (by norm_num : 0 < 2), sub_zero]
    rw [this, S.Tpol_hasse2_spec f _ xa]
    rw [← mul_one ((2 : R) ^ j * u), mul_assoc, S.pi_two_pow_mul _ hj]
  have h := S.class_count_gen hcard G xa c g (by rw [hGe]; exact hc) hGd (by rw [hπg]; exact hw)
    (S.k - j) (by omega) (by omega)
  rw [show S.k - (S.k - j) + 1 = j + 1 by omega, hG2, hπg] at h
  rw [← h]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hGe]

/-- **Theorem inter (ii), upper bounds.** -/
theorem inter_upper (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ)
    (hd2 : ∀ a b : K, (f.map S.π).derivative.eval a = (f.map S.π).derivative.eval b →
      b = a ∨ b = a + ρ)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j + 3 ≤ S.k) (u : R) (hu : S.π u ≠ 0)
    (hc3 : ∀ a, (hasseDeriv 3 (f.map S.π)).eval a = 0)
    (hp2 : ∀ a, (hasseDeriv 2 (f.map S.π)).eval a ≠ 0) (β : R) :
    delta f (2 ^ j * u) β ≤ 2 * Fintype.card K ^ (j + 1) ∧
      ((∀ a, S.Afun f ρ a + S.π (2 ^ (j - 1)) * S.π u * μ ≠ 0) →
        delta f (2 ^ j * u) β ≤ Fintype.card K ^ (j + 1)) := by
  by_cases h0 : delta f (2 ^ j * u) β = 0
  · rw [h0]; exact ⟨Nat.zero_le _, fun _ => Nat.zero_le _⟩
  obtain ⟨x0, hx0⟩ : ∃ x0, f.eval (x0 + 2 ^ j * u) - f.eval x0 = β := by
    by_contra hne
    push Not at hne
    apply h0
    unfold delta
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    exact hne x hx
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = (Tpol f (2 ^ j * u)).eval x0 := ⟨_, rfl⟩
  have hβ : β = 2 ^ j * u * γ := by rw [← hx0, hγ, Tpol_eval_mul]
  have hαπ : S.π ((2 : R) ^ j * u) = 0 := S.pi_two_pow_mul j hj u
  let C : K → Finset R := fun a => univ.filter (fun x : R => S.π x = a ∧
    ∃ w, (Tpol f (2 ^ j * u)).eval x - γ = 2 ^ (S.k - j) * w)
  have hcc : ∀ a, S.cc f (2 ^ j * u) β a = (C a).card := by
    intro a
    unfold cc
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Gpoly_eval, C]
    rw [← S.sol_iff f j (by omega) u γ x hu, hβ]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linear_combination h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linear_combination h2⟩
  have hk4 : ∀ w : R, (2 : R) ^ (S.k - j) * w = 4 * (2 ^ (S.k - j - 2) * w) := by
    intro w
    rw [show (4 : R) = 2 ^ 2 by norm_num, ← mul_assoc, ← pow_add]; congr 2; omega
  have hle : ∀ a, (C a).card ≤ Fintype.card K ^ (j + 1) := by
    intro a
    rcases (C a).eq_empty_or_nonempty with he | ⟨xa, hxa⟩
    · rw [he, Finset.card_empty]; exact Nat.zero_le _
    · simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hxa
      obtain ⟨hπa, w, hw⟩ := hxa
      have hw0 : S.π ((hasseDeriv 2 f).eval xa) + S.π (2 ^ (j - 1)) * S.π u *
          S.π ((hasseDeriv 3 f).eval xa) ≠ 0 := by
        rw [S.pi_hasse, S.pi_hasse, hc3, mul_zero, add_zero]; exact hp2 _
      have h := S.class_val hcard f j hj hjk u γ xa (2 ^ (S.k - j - 2) * w) (by rw [hw, hk4]) hw0
      have hC : C a = univ.filter (fun x : R => S.π x = S.π xa ∧
          ∃ w, (Tpol f (2 ^ j * u)).eval x - γ = 2 ^ (S.k - j) * w) := by
        simp only [C]; rw [← hπa]
      rw [hC, h]
      have h3 : S.π ((hasseDeriv 3 f).eval xa) = 0 := by rw [S.pi_hasse]; exact hc3 _
      rw [h3]
      simp only [mul_zero, add_zero, zero_mul]
      have := roots_lin (S.π ((hasseDeriv 2 f).eval xa)) (S.π (2 ^ (S.k - j - 2) * w))
        (by rw [S.pi_hasse]; exact hp2 _)
      simp only [zero_mul, add_zero] at this
      rw [this, mul_one]
  have hgate : ∀ a, (C a).Nonempty → a = S.π x0 ∨ a = S.π x0 + ρ := by
    rintro a ⟨x, hx⟩
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hπa, w, hw⟩ := hx
    have h1 : S.π ((Tpol f (2 ^ j * u)).eval x) = S.π γ := by
      have : S.π ((Tpol f (2 ^ j * u)).eval x - γ) = 0 := by
        rw [hw]; exact S.pi_two_pow_mul _ (by omega) _
      rwa [map_sub, sub_eq_zero] at this
    rw [S.Tpol_pi f _ x hαπ, hγ, S.Tpol_pi f _ x0 hαπ, hπa] at h1
    exact hd2 (S.π x0) a h1.symm
  have hne : S.π x0 ≠ S.π x0 + ρ := by intro h; apply H.hρ; linear_combination -h
  have hsum : delta f (2 ^ j * u) β = (C (S.π x0)).card + (C (S.π x0 + ρ)).card := by
    rw [S.delta_eq_sum]
    simp_rw [hcc]
    rw [show (C (S.π x0)).card + (C (S.π x0 + ρ)).card =
        ∑ a ∈ ({S.π x0, S.π x0 + ρ} : Finset K), (C a).card from (Finset.sum_pair (f := fun a => (C a).card) hne).symm]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    rcases (C a).eq_empty_or_nonempty with he | hne'
    · rw [he, Finset.card_empty]
    · exact absurd (by rcases hgate a hne' with h | h <;> simp [h]) ha
  constructor
  · rw [hsum]
    have h1 := hle (S.π x0)
    have h2 := hle (S.π x0 + ρ)
    omega
  · intro hB
    have hempty : C (S.π x0 + ρ) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x' hx'
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      obtain ⟨hπx', w', hw'⟩ := hx'
      obtain ⟨g, hg, hπg⟩ := S.Tpol_pair f ρ μ H j hj u x0 (x' - x0) (by rw [map_sub, hπx']; ring)
      have e : x0 + (x' - x0) = x' := by ring
      rw [e] at hg
      have h4 : 2 * g = 2 * (2 * (2 ^ (S.k - j - 2) * w')) := by
        linear_combination -hg + hw' + hγ + hk4 w'
      have := S.pi_eq_of_two_mul_eq h4
      rw [S.pi_two_mul, hπg] at this
      exact hB _ this
    rw [hsum, hempty, Finset.card_empty, add_zero]
    exact hle _

end card

end GRS

end APN2

#print axioms APN2.GRS.class_count_gen
#print axioms APN2.GRS.inter_upper
