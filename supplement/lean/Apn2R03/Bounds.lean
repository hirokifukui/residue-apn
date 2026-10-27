import Apn2R03.Pair
import Apn2R03.Cards

/-!
# Upper and lower bounds for exceptional rows (Claude, 2026-10-25)

`Hyp` collects the consequences of (H) used in the paper (FOUNDATIONS F0):
ρ ≠ 0, p'(a+ρ) = p'(a), p^[2](a+ρ) − p^[2](a) = μ, and D_ρ p is exactly 2-to-1 on pairs {a, a+ρ}.

Lower bounds (M1) and upper bounds (consequences of the local formula) for δ(α, β), α exceptional.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)

structure Hyp (f : R[X]) (ρ μ : K) : Prop where
  hρ : ρ ≠ 0
  hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) = (f.map S.π).derivative.eval a
  hμ : ∀ a, (hasseDeriv 2 (f.map S.π)).eval (a + ρ) - (hasseDeriv 2 (f.map S.π)).eval a = μ
  hdp : ∀ a b : K, (f.map S.π).eval (a + ρ) - (f.map S.π).eval a =
      (f.map S.π).eval (b + ρ) - (f.map S.π).eval b ↔ (b = a ∨ b = a + ρ)

theorem charP2 (S : GRS R K) : CharP K 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero S.two_F

section card
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem cc_le_delta (f : R[X]) (α β : R) (a : K) : S.cc f α β a ≤ delta f α β := by
  rw [S.delta_eq_sum]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem two_cc_le_delta (f : R[X]) (α β : R) (a b : K) (hab : a ≠ b) :
    S.cc f α β a + S.cc f α β b ≤ delta f α β := by
  rw [S.delta_eq_sum]
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun c => S.cc f α β c)
    (Finset.subset_univ ({a, b} : Finset K)) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hab] at this
  exact this

theorem roots_eq_nfib (S : GRS R K) (μ A c : K) :
    (univ.filter (fun y : K => c + A * y + μ * y ^ 2 = 0)).card = APN2R03.nfib μ A c := by
  unfold APN2R03.nfib
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 := S.two_F
  constructor
  · intro h; linear_combination h - c * h2
  · intro h; linear_combination h + c * h2

theorem roots_le_two (S : GRS R K) (μ A c : K) (hμ : μ ≠ 0) (hA : A ≠ 0) :
    (univ.filter (fun y : K => c + A * y + μ * y ^ 2 = 0)).card ≤ 2 := by
  haveI := S.charP2
  rw [S.roots_eq_nfib, APN2R03.nfib_eq μ A c hμ hA]
  split_ifs <;> norm_num

theorem roots_lin (A c : K) (hA : A ≠ 0) :
    (univ.filter (fun y : K => c + A * y + 0 * y ^ 2 = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨-c / A, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, zero_mul, add_zero]
  constructor
  · intro h; field_simp; linear_combination h
  · intro h; rw [h]; field_simp; ring

theorem delta_set_eq (f : R[X]) (α β : R) :
    univ.filter (fun x : R => f.eval (x + α) - f.eval x = β) =
      univ.filter (fun x : R => (Gpoly f α β).eval x = 0) := by
  ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Gpoly_eval]
  constructor
  · intro h; rw [h]; ring
  · intro h; linear_combination h

theorem two_pow_mul_sq_eq_zero (j : ℕ) (hj : S.k ≤ 2 * j) (y : R) : (2 ^ j * y) ^ 2 = 0 := by
  have : (2 : R) ^ (2 * j) = 0 := by
    obtain ⟨d, hd⟩ : ∃ d, 2 * j = S.k + d := ⟨2 * j - S.k, by omega⟩
    rw [hd, pow_add, S.nil, zero_mul]
  rw [mul_pow, ← pow_mul, mul_comm j 2, this, zero_mul]

/-! ## lower bounds (M1) -/

/-- M1(i): every lift has an exceptional entry ≥ q -/
theorem lower_q (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ) :
    ∃ β, Fintype.card K ≤ delta f α β := by
  set xa := S.L 0
  set β := f.eval (xa + α) - f.eval xa
  refine ⟨β, ?_⟩
  rw [← S.card_ann_two hcard]
  unfold delta
  rw [delta_set_eq]
  apply Finset.card_le_card_of_injOn (fun w => xa + w)
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw ⊢
    obtain ⟨g, hg⟩ := S.D_even f ρ H.hper xa α hα
    obtain ⟨Q, hQ⟩ := taylor2 (Gpoly f α β) xa w
    obtain ⟨y, hy⟩ := S.tors w hw
    have hw2 : w ^ 2 = 0 := by
      rw [hy]; exact S.two_pow_mul_sq_eq_zero (S.k - 1) (by have := S.hk; omega) y
    rw [hQ, Gpoly_eval, Gpoly_deriv_eval, hg, hw2]
    have : w * (2 * g) = (2 * w) * g := by ring
    rw [this, hw]; ring
  · intro w _ w' _ h; simpa using h

/-- M1(ii): if Λ has a zero, some exceptional entry is ≥ 2q -/
theorem lower_2q (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ) (a : K) (hL : S.Lam f ρ a = 0) :
    ∃ β, 2 * Fintype.card K ≤ delta f α β := by
  classical
  have hk := S.hk
  set xa := S.L a
  have hxa : S.π xa = a := S.pi_L a
  set b := f.eval (xa + α) - f.eval xa
  set s := univ.filter (fun x : R => S.π x = a ∨ S.π x = a + ρ)
  set t := (I (R := R) 2).image (fun z => b + z)
  set φ := fun x : R => f.eval (x + α) - f.eval x
  -- G0 with β = 0
  have hstep : ∀ x0 z : R, ∃ w, φ (x0 + 2 * z) = φ x0 + 4 * w := by
    intro x0 z
    obtain ⟨g, hg⟩ := S.D_even f ρ H.hper x0 α hα
    obtain ⟨Q, hQ⟩ := taylor2 (Gpoly f α 0) x0 (2 * z)
    rw [Gpoly_eval, Gpoly_eval, Gpoly_deriv_eval, hg] at hQ
    exact ⟨z * g + z ^ 2 * Q, by simp only [φ]; linear_combination hQ⟩
  have hmaps : ∀ x ∈ s, φ x ∈ t := by
    intro x hx
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [t, Finset.mem_image, mem_I]
    rcases hx with hx | hx
    · obtain ⟨z, hz⟩ := S.sub_two_of_pi_eq (y := x) (y' := xa) (by rw [hx, hxa])
      obtain ⟨w, hw⟩ := hstep xa z
      refine ⟨4 * w, ⟨w, by norm_num⟩, ?_⟩
      have : x = xa + 2 * z := by linear_combination hz
      rw [this, hw]
    · obtain ⟨z, hz⟩ := S.sub_two_of_pi_eq (y := x) (y' := xa + α) (by rw [hx, map_add, hxa, hα])
      obtain ⟨w, hw⟩ := hstep (xa + α) z
      obtain ⟨c, hc⟩ := S.S_div4 f ρ xa α a hxa hα hL
      refine ⟨4 * (w + c), ⟨w + c, by norm_num⟩, ?_⟩
      have : x = xa + α + 2 * z := by linear_combination hz
      rw [this, hw]
      unfold Sx at hc
      simp only [φ, b]
      have e : xa + α + α = xa + 2 * α := by ring
      rw [e]
      linear_combination -hc
  have hs : s.card = 2 * Fintype.card K ^ (S.k - 1) := by
    have hdisj : Disjoint (univ.filter (fun x : R => S.π x = a))
        (univ.filter (fun x : R => S.π x = a + ρ)) := by
      rw [Finset.disjoint_filter]
      intro x _ h1 h2
      apply H.hρ
      linear_combination h1 - h2
    have : s = univ.filter (fun x : R => S.π x = a) ∪ univ.filter (fun x : R => S.π x = a + ρ) := by
      ext x; simp [s]
    rw [this, Finset.card_union_of_disjoint hdisj, S.card_fiber hcard, S.card_fiber hcard]
    ring
  have ht : t.card = Fintype.card K ^ (S.k - 2) := S.card_coset hcard 2 (by omega) b
  have hn : t.card * (2 * Fintype.card K) ≤ s.card := by
    rw [hs, ht]
    have : Fintype.card K ^ (S.k - 2) * Fintype.card K = Fintype.card K ^ (S.k - 1) := by
      rw [← pow_succ]; congr 1; omega
    nlinarith [this]
  have htne : t.Nonempty := ⟨b + 0, Finset.mem_image.mpr ⟨0, (mem_I 2 0).mpr ⟨0, by ring⟩, rfl⟩⟩
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps htne hn
  refine ⟨y, le_trans hy ?_⟩
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hx.2

/-- M1(iii): for k ≥ 4, a zero of A forces an exceptional entry ≥ q² -/
theorem lower_q2 (hcard : Fintype.card R = Fintype.card K ^ S.k) (hk4 : 4 ≤ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ) (α : R) (hα : S.π α = ρ) (a : K) (hA : S.Afun f ρ a = 0) :
    ∃ β, Fintype.card K ^ 2 ≤ delta f α β := by
  set xa := S.L a
  set β := f.eval (xa + α) - f.eval xa
  refine ⟨β, ?_⟩
  have hI := S.card_I hcard (S.k - 2) (by omega)
  rw [show S.k - (S.k - 2) = 2 by omega] at hI
  rw [← hI]
  unfold delta
  rw [delta_set_eq]
  obtain ⟨g, hg, hπg⟩ := S.A_spec f ρ H.hper xa α a (S.pi_L a) hα
  rw [hA] at hπg
  obtain ⟨g', hg'⟩ := (S.ker2 g).mp hπg
  apply Finset.card_le_card_of_injOn (fun h => xa + h)
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.mem_coe] at hh ⊢
    obtain ⟨y, rfl⟩ := (mem_I _ h).mp hh
    obtain ⟨Q, hQ⟩ := taylor2 (Gpoly f α β) xa (2 ^ (S.k - 2) * y)
    have hsq := S.two_pow_mul_sq_eq_zero (S.k - 2) (by omega) y
    rw [hQ, Gpoly_eval, Gpoly_deriv_eval, hg, hg', hsq]
    have : (2 : R) ^ (S.k - 2) * y * (2 * (2 * g')) = 2 ^ S.k * (y * g') := by
      have e : (2 : R) ^ S.k = 2 ^ (S.k - 2) * 2 ^ 2 := by
        rw [← pow_add]; congr 1; omega
      rw [e]; ring
    rw [this, S.nil]; ring
  · intro h _ h' _ hh; simpa using hh

/-- one class with A(a) ≠ 0 and μ ≠ 0 gives an entry ≥ 2q -/
theorem lower_2q_A (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0) (α : R) (hα : S.π α = ρ) (a : K) (hA : S.Afun f ρ a ≠ 0) :
    ∃ β, 2 * Fintype.card K ≤ delta f α β := by
  set xa := S.L a
  have hxa : S.π xa = a := S.pi_L a
  set β := f.eval (xa + α) - f.eval xa
  refine ⟨β, le_trans ?_ (S.cc_le_delta f α β a)⟩
  have h0 : (Gpoly f α β).eval xa = 4 * 0 := by rw [Gpoly_eval]; ring
  have hcc := S.cc_formula hcard f ρ μ H.hper H.hμ α β xa 0 hα h0 (by rw [hxa]; exact hA)
  rw [hxa] at hcc
  rw [hcc, map_zero, mul_comm]
  apply Nat.mul_le_mul_left
  have hsub : ({0, S.Afun f ρ a / μ} : Finset K) ⊆
      univ.filter (fun y : K => 0 + S.Afun f ρ a * y + μ * y ^ 2 = 0) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl
    · ring
    · field_simp; have h2 := S.two_F; linear_combination (S.Afun f ρ a) ^ 2 * h2
  have hne : (0 : K) ≠ S.Afun f ρ a / μ := (div_ne_zero hA hμ0).symm
  calc 2 = ({0, S.Afun f ρ a / μ} : Finset K).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- M1(iv): k ≥ 4 and μ ≠ 0 force an entry ≥ 2q -/
theorem lower_2q_k4 (hcard : Fintype.card R = Fintype.card K ^ S.k) (hk4 : 4 ≤ S.k) (f : R[X])
    (ρ μ : K) (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0) (α : R) (hα : S.π α = ρ) :
    ∃ β, 2 * Fintype.card K ≤ delta f α β := by
  by_cases hA : S.Afun f ρ 0 = 0
  · obtain ⟨β, hβ⟩ := S.lower_q2 hcard hk4 f ρ μ H α hα 0 hA
    refine ⟨β, le_trans ?_ hβ⟩
    have hq : 2 ≤ Fintype.card K := by
      have : (0 : K) ≠ 1 := zero_ne_one
      exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    nlinarith
  · exact S.lower_2q_A hcard f ρ μ H hμ0 α hα 0 hA

/-- a Λ-zero pair with A ≠ 0 and χ = 0 (E ∈ Im L) gives an entry ≥ 4q -/
theorem lower_4q (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0) (α : R) (hα : S.π α = ρ) (a : K) (hA : S.Afun f ρ a ≠ 0)
    (hL : S.Lam f ρ a = 0) (hE : S.Efun f ρ a ∈ APN2R03.qimg μ (S.Afun f ρ a)) :
    ∃ β, 4 * Fintype.card K ≤ delta f α β := by
  haveI := S.charP2
  set xa := S.L a
  have hxa : S.π xa = a := S.pi_L a
  set β := f.eval (xa + α) - f.eval xa
  refine ⟨β, ?_⟩
  have hne : a ≠ a + ρ := by intro h; apply H.hρ; linear_combination -h
  refine le_trans ?_ (S.two_cc_le_delta f α β a (a + ρ) hne)
  have h0 : (Gpoly f α β).eval xa = 4 * 0 := by rw [Gpoly_eval]; ring
  have hcc1 := S.cc_formula hcard f ρ μ H.hper H.hμ α β xa 0 hα h0 (by rw [hxa]; exact hA)
  rw [hxa] at hcc1
  obtain ⟨c', hc', hπc'⟩ := S.cc_shift f ρ H.hper α β xa 0 hα (by rw [hxa]; exact hL) h0
  have hxb : S.π (xa + α) = a + ρ := by rw [map_add, hxa, hα]
  have hAb : S.Afun f ρ (S.π (xa + α)) ≠ 0 := by
    rw [hxb, S.A_periodic f ρ H.hper]; exact hA
  have hcc2 := S.cc_formula hcard f ρ μ H.hper H.hμ α β (xa + α) c' hα hc' hAb
  rw [hxb, S.A_periodic f ρ H.hper, hπc', hxa, map_zero, zero_add] at hcc2
  rw [hcc1, hcc2, map_zero, S.roots_eq_nfib, S.roots_eq_nfib,
    APN2R03.nfib_eq μ _ _ hμ0 hA, APN2R03.nfib_eq μ _ _ hμ0 hA, if_pos hE]
  have h0mem : (0 : K) ∈ APN2R03.qimg μ (S.Afun f ρ a) := by
    unfold APN2R03.qimg; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨0, by ring⟩
  rw [if_pos h0mem]
  ring_nf
  exact le_refl _

/-! ## upper bounds -/

theorem cc_le (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (α β : R) (hα : S.π α = ρ) (x : R) (hA : S.Afun f ρ (S.π x) ≠ 0) :
    S.cc f α β (S.π x) ≤ Fintype.card K * (if μ = 0 then 1 else 2) := by
  by_cases hc : ∃ c, (Gpoly f α β).eval x = 4 * c
  · obtain ⟨c, hc⟩ := hc
    rw [S.cc_formula hcard f ρ μ H.hper H.hμ α β x c hα hc hA]
    apply Nat.mul_le_mul_left
    split_ifs with hμ0
    · subst hμ0; rw [roots_lin _ _ hA]
    · exact S.roots_le_two μ _ _ hμ0 hA
  · rw [S.cc_zero f ρ H.hper α β x hα hc]; exact Nat.zero_le _

/-- reduction of a row entry to the pair with canonical lift `L a₀` and `L a₀ + α` -/
theorem delta_pair' (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (α β : R) (hα : S.π α = ρ) :
    delta f α β = 0 ∨ ∃ a0 : K, delta f α β = S.cc f α β (S.π (S.L a0)) + S.cc f α β (S.π (S.L a0 + α)) := by
  by_cases h : ∃ a0 : K, (f.map S.π).eval (a0 + ρ) - (f.map S.π).eval a0 = S.π β
  · obtain ⟨a0, ha0⟩ := h
    right
    refine ⟨a0, ?_⟩
    rw [S.delta_pair f α β ρ hα H.hρ H.hdp a0 ha0, map_add, S.pi_L, hα]
  · left
    apply S.delta_no_pair
    intro a ha
    exact h ⟨a, by rw [← hα]; exact ha⟩

/-- U1/U2: with A nowhere zero, entries are ≤ 4q (μ ≠ 0) and ≤ 2q (μ = 0) -/
theorem upper_basic (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ μ : K)
    (H : S.Hyp f ρ μ) (hA : ∀ a, S.Afun f ρ a ≠ 0) (α β : R) (hα : S.π α = ρ) :
    delta f α β ≤ 2 * Fintype.card K * (if μ = 0 then 1 else 2) := by
  rcases S.delta_pair' f ρ μ H α β hα with h | ⟨a0, h⟩
  · rw [h]; exact Nat.zero_le _
  · rw [h]
    have h1 := S.cc_le hcard f ρ μ H α β hα (S.L a0) (hA _)
    have h2 := S.cc_le hcard f ρ μ H α β hα (S.L a0 + α) (hA _)
    linarith

/-- second class fails the gate whenever the first fails it, on a Λ-zero pair -/
theorem gate_same (f : R[X]) (ρ : K) (_hper : ∀ a, (f.map S.π).derivative.eval (a + ρ) =
      (f.map S.π).derivative.eval a)
    (α β xa : R) (hα : S.π α = ρ) (hL : S.Lam f ρ (S.π xa) = 0)
    (hnot : ¬ ∃ c, (Gpoly f α β).eval xa = 4 * c) : ¬ ∃ c, (Gpoly f α β).eval (xa + α) = 4 * c := by
  rintro ⟨c, hc⟩
  obtain ⟨e, he⟩ := S.S_div4 f ρ xa α (S.π xa) rfl hα hL
  apply hnot
  refine ⟨c - e, ?_⟩
  rw [Gpoly_eval] at hc ⊢
  unfold Sx at he
  have e1 : xa + α + α = xa + 2 * α := by ring
  rw [e1] at hc
  linear_combination hc - he

/-- U3: μ = 0, A nowhere zero, Λ nowhere zero ⇒ entries ≤ q -/
theorem upper_mu0_Zempty (hcard : Fintype.card R = Fintype.card K ^ S.k) (f : R[X]) (ρ : K)
    (H : S.Hyp f ρ 0) (hA : ∀ a, S.Afun f ρ a ≠ 0) (hZ : ∀ a, S.Lam f ρ a ≠ 0)
    (α β : R) (hα : S.π α = ρ) : delta f α β ≤ Fintype.card K := by
  rcases S.delta_pair' f ρ 0 H α β hα with h | ⟨a0, h⟩
  · rw [h]; exact Nat.zero_le _
  · rw [h]
    have h1 := S.cc_le hcard f ρ 0 H α β hα (S.L a0) (hA _)
    have h2 := S.cc_le hcard f ρ 0 H α β hα (S.L a0 + α) (hA _)
    simp only [if_true, mul_one] at h1 h2
    by_cases hc : ∃ c, (Gpoly f α β).eval (S.L a0) = 4 * c
    · obtain ⟨c, hc⟩ := hc
      have := S.gate_exclusive f ρ H.hper α β (S.L a0) c hα (hZ _) hc
      rw [S.cc_zero f ρ H.hper α β (S.L a0 + α) hα this]
      linarith
    · rw [S.cc_zero f ρ H.hper α β (S.L a0) hα hc]
      linarith

/-- U4: μ ≠ 0, A nowhere zero, χ = 1 on Z (E ∉ Im L) ⇒ entries ≤ 2q -/
theorem upper_mu_chi1 (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ)
    (hm : Fintype.card K = 2 ^ m) (f : R[X]) (ρ μ : K) (H : S.Hyp f ρ μ) (hμ0 : μ ≠ 0)
    (hA : ∀ a, S.Afun f ρ a ≠ 0)
    (hχ : ∀ a, S.Lam f ρ a = 0 → S.Efun f ρ a ∉ APN2R03.qimg μ (S.Afun f ρ a))
    (α β : R) (hα : S.π α = ρ) : delta f α β ≤ 2 * Fintype.card K := by
  haveI := S.charP2
  rcases S.delta_pair' f ρ μ H α β hα with h | ⟨a0, h⟩
  · rw [h]; exact Nat.zero_le _
  · rw [h]
    have h1 := S.cc_le hcard f ρ μ H α β hα (S.L a0) (hA _)
    have h2 := S.cc_le hcard f ρ μ H α β hα (S.L a0 + α) (hA _)
    simp only [hμ0, if_false] at h1 h2
    set xa := S.L a0
    have hxa : S.π xa = a0 := S.pi_L a0
    by_cases hL : S.Lam f ρ a0 = 0
    · by_cases hc : ∃ c, (Gpoly f α β).eval xa = 4 * c
      · obtain ⟨c, hc⟩ := hc
        obtain ⟨c', hc', hπc'⟩ := S.cc_shift f ρ H.hper α β xa c hα (by rw [hxa]; exact hL) hc
        have hcc1 := S.cc_formula hcard f ρ μ H.hper H.hμ α β xa c hα hc (hA _)
        have hcc2 := S.cc_formula hcard f ρ μ H.hper H.hμ α β (xa + α) c' hα hc' (hA _)
        have hxb : S.π (xa + α) = a0 + ρ := by rw [map_add, hxa, hα]
        rw [hcc1, hcc2, hxb, S.A_periodic f ρ H.hper, hπc', hxa, S.roots_eq_nfib, S.roots_eq_nfib,
          ← mul_add]
        have := (APN2R03.local_pair_count m hm μ (S.Afun f ρ a0) (S.Efun f ρ a0) hμ0 (hA a0)).2
          (hχ a0 hL) (S.π c)
        rw [this]; ring_nf; exact le_refl _
      · rw [S.cc_zero f ρ H.hper α β xa hα hc,
          S.cc_zero f ρ H.hper α β (xa + α) hα (S.gate_same f ρ H.hper α β xa hα
            (by rw [hxa]; exact hL) hc)]
        exact Nat.zero_le _
    · by_cases hc : ∃ c, (Gpoly f α β).eval xa = 4 * c
      · obtain ⟨c, hc⟩ := hc
        have := S.gate_exclusive f ρ H.hper α β xa c hα (by rw [hxa]; exact hL) hc
        rw [S.cc_zero f ρ H.hper α β (xa + α) hα this]
        linarith
      · rw [S.cc_zero f ρ H.hper α β xa hα hc]
        linarith

end card

end GRS

end APN2

#print axioms APN2.GRS.lower_q
#print axioms APN2.GRS.lower_2q
#print axioms APN2.GRS.lower_q2
#print axioms APN2.GRS.lower_2q_k4
#print axioms APN2.GRS.lower_4q
#print axioms APN2.GRS.upper_basic
#print axioms APN2.GRS.upper_mu0_Zempty
#print axioms APN2.GRS.upper_mu_chi1
