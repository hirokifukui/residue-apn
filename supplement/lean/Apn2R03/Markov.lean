import Mathlib

/-!
# Markov property of key-alternating rounds (Claude, 2026-10-25, R04 follow-up; paper Prop. markov, C3')

State space: a finite additive group `G`. One round is `x ↦ M (S x) + κ` with an arbitrary map `S : G → G`
(the S-box layer), an additive automorphism `M` (the linear layer) and a round key `κ ∈ G`.
A vector `v : Fin (n+1) → G` is `(x₀, κ₁, …, κₙ)`: the starting state followed by the round keys.
`lastSt n v` is the state after round `n`. A characteristic is `Δ : ℕ → G`.
`trail Δ n v` says that the pair `(x₀, x₀ + Δ 0)` follows `Δ 0 → Δ 1 → ⋯ → Δ n` under the keys of `v`
(`round_diff` shows that the round-`i` condition is exactly "the output difference is `Δ i`").

* `trail_card`  : #{v | trail} = |G| · ∏_{i<n} dd S (Δ i) (M⁻¹ Δ (i+1)).
  Equivalently, for a uniform starting state independent of independent uniform keys,
  Pr[trail] = ∏ dd/|G| (`trail_prob`): the Markov product formula.
* `dd_pi` : for an S-box layer acting wordwise on `ι → R`, dd factorizes over the words.
* `trail_card_le` : the product bound from per-round bounds.
No probability theory is used: probabilities are counts over all `(x₀, κ₁, …, κₙ)`.
-/


set_option linter.unusedSectionVars false

namespace APN2.Markov

open Finset

open scoped Classical

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- difference table entry of `S` -/
noncomputable def dd (S : G → G) (a b : G) : ℕ := Fintype.card {x : G // S (x + a) - S x = b}

/-- state after round `n` from `v = (x₀, κ₁, …, κₙ)` -/
def lastSt (S : G → G) (M : G ≃+ G) : (n : ℕ) → (Fin (n + 1) → G) → G
  | 0, v => v 0
  | n + 1, v => M (S (lastSt S M n (Fin.init v))) + v (Fin.last (n + 1))

/-- the pair `(x₀, x₀ + Δ 0)` follows `Δ 0 → ⋯ → Δ n` -/
def trail (S : G → G) (M : G ≃+ G) (Δ : ℕ → G) : (n : ℕ) → (Fin (n + 1) → G) → Prop
  | 0, _ => True
  | n + 1, v => trail S M Δ n (Fin.init v) ∧
      S (lastSt S M n (Fin.init v) + Δ n) - S (lastSt S M n (Fin.init v)) = M.symm (Δ (n + 1))

/-- the round condition is "output difference = next difference" (the round key cancels) -/
theorem round_diff (S : G → G) (M : G ≃+ G) (x d d' κ : G) :
    (M (S (x + d)) + κ) - (M (S x) + κ) = d' ↔ S (x + d) - S x = M.symm d' := by
  constructor
  · intro h
    rw [← h, add_sub_add_right_eq_sub, ← map_sub, AddEquiv.symm_apply_apply]
  · intro h
    rw [add_sub_add_right_eq_sub, ← map_sub, h, AddEquiv.apply_symm_apply]

/-- the generalized count: an extra predicate on the final state -/
theorem trail_card_gen (S : G → G) (M : G ≃+ G) (Δ : ℕ → G) :
    ∀ (n : ℕ) (P : G → Prop) [DecidablePred P],
      Fintype.card {v : Fin (n + 1) → G // trail S M Δ n v ∧ P (lastSt S M n v)} =
        Fintype.card {a : G // P a} * ∏ i ∈ range n, dd S (Δ i) (M.symm (Δ (i + 1))) := by
  intro n
  induction n with
  | zero =>
    intro P _
    simp only [range_zero, prod_empty, mul_one]
    apply Fintype.card_congr
    exact
      { toFun := fun v => ⟨v.1 0, v.2.2⟩
        invFun := fun a => ⟨fun _ => a.1, trivial, a.2⟩
        left_inv := by
          intro v; apply Subtype.ext; funext i; fin_cases i; rfl
        right_inv := by intro a; rfl }
  | succ n ih =>
    intro P _
    classical
    let D : G → Prop := fun y => S (y + Δ n) - S y = M.symm (Δ (n + 1))
    have hE : {v : Fin (n + 1 + 1) → G // trail S M Δ (n + 1) v ∧ P (lastSt S M (n + 1) v)} ≃
        {w : Fin (n + 1) → G // trail S M Δ n w ∧ D (lastSt S M n w)} × {a : G // P a} :=
      { toFun := fun v => (⟨Fin.init v.1, v.2.1⟩, ⟨lastSt S M (n + 1) v.1, v.2.2⟩)
        invFun := fun p => ⟨Fin.snoc (α := fun _ => G) p.1.1 (p.2.1 - M (S (lastSt S M n p.1.1))), by
          refine ⟨?_, ?_⟩
          · show trail S M Δ n (Fin.init (α := fun _ => G) _) ∧ _
            rw [Fin.init_snoc]; exact p.1.2
          · show P (M (S (lastSt S M n (Fin.init (α := fun _ => G) _))) + _)
            rw [Fin.init_snoc, Fin.snoc_last, add_sub_cancel]; exact p.2.2⟩
        left_inv := by
          intro v
          apply Subtype.ext
          show Fin.snoc (α := fun _ => G) (Fin.init v.1)
            (M (S (lastSt S M n (Fin.init v.1))) + v.1 (Fin.last (n + 1)) -
              M (S (lastSt S M n (Fin.init v.1)))) = v.1
          rw [add_sub_cancel_left, Fin.snoc_init_self]
        right_inv := by
          intro p
          apply Prod.ext
          · apply Subtype.ext
            show Fin.init (Fin.snoc (α := fun _ => G) p.1.1 _) = p.1.1
            rw [Fin.init_snoc]
          · apply Subtype.ext
            show M (S (lastSt S M n (Fin.init (Fin.snoc (α := fun _ => G) p.1.1 _)))) +
              Fin.snoc (α := fun _ => G) p.1.1 _ (Fin.last (n + 1)) = p.2.1
            rw [Fin.init_snoc, Fin.snoc_last, add_sub_cancel] }
    rw [Fintype.card_congr hE, Fintype.card_prod, ih D, prod_range_succ]
    have hD : Fintype.card {a : G // D a} = dd S (Δ n) (M.symm (Δ (n + 1))) := by
      unfold dd; rfl
    rw [hD]; ring

/-- **Markov product formula (count form).** -/
theorem trail_card (S : G → G) (M : G ≃+ G) (Δ : ℕ → G) (n : ℕ) :
    Fintype.card {v : Fin (n + 1) → G // trail S M Δ n v} =
      Fintype.card G * ∏ i ∈ range n, dd S (Δ i) (M.symm (Δ (i + 1))) := by
  classical
  have h := trail_card_gen S M Δ n (fun _ => True)
  have h1 : Fintype.card {v : Fin (n + 1) → G // trail S M Δ n v ∧ True} =
      Fintype.card {v : Fin (n + 1) → G // trail S M Δ n v} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun v => by simp))
  have h2 : Fintype.card {a : G // True} = Fintype.card G := Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))
  rw [← h1, h, h2]

/-- **Markov product formula (probability form)**: uniform `(x₀, κ₁, …, κₙ)` on `G^(n+1)`. -/
theorem trail_prob (S : G → G) (M : G ≃+ G) (Δ : ℕ → G) (n : ℕ) :
    (Fintype.card {v : Fin (n + 1) → G // trail S M Δ n v} : ℚ) / (Fintype.card (Fin (n + 1) → G) : ℚ) =
      ∏ i ∈ range n, ((dd S (Δ i) (M.symm (Δ (i + 1))) : ℚ) / Fintype.card G) := by
  have hG : (Fintype.card G : ℚ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [trail_card, Fintype.card_fun, Fintype.card_fin, prod_div_distrib, prod_const, card_range]
  push_cast
  rw [pow_succ]
  field_simp

/-- product bound from per-round bounds -/
theorem trail_card_le (S : G → G) (M : G ≃+ G) (Δ : ℕ → G) (n : ℕ) (b : ℕ → ℕ)
    (hb : ∀ i < n, dd S (Δ i) (M.symm (Δ (i + 1))) ≤ b i) :
    Fintype.card {v : Fin (n + 1) → G // trail S M Δ n v} ≤ Fintype.card G * ∏ i ∈ range n, b i := by
  rw [trail_card]
  apply Nat.mul_le_mul_left
  apply prod_le_prod' 
  intro i hi
  exact hb i (mem_range.mp hi)

/-- an S-box layer acting wordwise: the difference table factorizes over the words -/
theorem dd_pi {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup R] [Fintype R] [DecidableEq R]
    (F : R → R) (a b : ι → R) :
    dd (fun x : ι → R => fun j => F (x j)) a b = ∏ j, dd F (a j) (b j) := by
  unfold dd
  rw [← Fintype.card_pi]
  apply Fintype.card_congr
  refine (Equiv.subtypeEquivRight (fun x => ?_)).trans (Equiv.subtypePiEquivPi)
  simp only [funext_iff, Pi.sub_apply, Pi.add_apply]

/-- branch-number counting: if consecutive rounds together have at least `B` active S-boxes,
then `N` rounds have at least `B ⌊N/2⌋` (paper, proof of Cor. crypto) -/
theorem sum_active_ge (a : ℕ → ℕ) (B : ℕ) (h : ∀ i, B ≤ a i + a (i + 1)) :
    ∀ N, B * (N / 2) ≤ ∑ i ∈ range N, a i := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp
    | 1 => simp
    | N + 2 =>
      have h1 := ih N (by omega)
      rw [sum_range_succ, sum_range_succ]
      have h2 : (N + 2) / 2 = N / 2 + 1 := by omega
      rw [h2, Nat.mul_succ]
      have := h N
      omega

/-- the resulting bound: each of at least `B ⌊N/2⌋` active S-boxes contributes a factor `≤ p`,
the others `≤ 1` (stated for probabilities in `[0,1]`) -/
theorem prod_le_pow_of_active (N B : ℕ) (P : ℕ → ℚ) (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ → ℕ) (hk : B * (N / 2) ≤ ∑ i ∈ range N, k i)
    (hP : ∀ i < N, 0 ≤ P i ∧ P i ≤ p ^ k i) :
    ∏ i ∈ range N, P i ≤ p ^ (B * (N / 2)) := by
  calc ∏ i ∈ range N, P i ≤ ∏ i ∈ range N, p ^ k i := by
        apply prod_le_prod
        · intro i hi; exact (hP i (mem_range.mp hi)).1
        · intro i hi; exact (hP i (mem_range.mp hi)).2
    _ = p ^ (∑ i ∈ range N, k i) := by rw [prod_pow_eq_pow_sum]
    _ ≤ p ^ (B * (N / 2)) := pow_le_pow_of_le_one hp0 hp1 hk

end APN2.Markov
