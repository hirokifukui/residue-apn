import ResidueAPN.Basic

/-!
# Proposition 6.1 and Theorem 6.2 (R) of paper_R5 — coefficient lifts over a finite local ring

Abstract setting (it holds for `R = GR(2^k, m)`, `F = 𝔽_q`, `π` the residue map):
* `R` a finite commutative ring, `F` a finite field, `π : R →+* F` surjective;
* `hunit : ∀ u, π u ≠ 0 → IsUnit u` (`R` is local with maximal ideal `ker π`).
For Theorem 6.2(2) an element `α` with `hann : ∀ r, α * r = 0 ↔ π r = 0` (in `GR(2^k,m)`, `k ≥ 2`, these are
exactly the nonzero elements of the top ideal `2^(k-1) R`, whose annihilator is `2R = ker π`).
A coefficient lift of `p ∈ F[X]` is any `G ∈ R[X]` with `G.map π = p`.

* `prop_6_1`: if `p` permutes `F` and `p'` has no zero on `F`, every coefficient lift permutes `R`.
* `thm_6_2_unit`: if `p'(t + a) − p'(t) ≠ 0` for all `t` (`a = π α`; for quadratic `p` this is `a ∉ ker K`),
  then `#{x ∈ R : G(x+α) − G(x) = β} = #{t ∈ F : p(t+a) − p(t) = π β}`.
* `thm_6_2_top`: if every fibre of `t ↦ p'(t)` has two elements, every nonzero entry
  `#{x : G(x+α) − G(x) = β}` equals `2 · #(ker π)`; with `#R = q^k`, `#F = q` this is `2 q^(k-1)`
  (`card_ker_mul`).
Not formalized: the identification of these hypotheses with `GR(2^k, m)` (no Galois rings in Mathlib), and the
bounds quoted from Rønjom–Sandrib after Theorem 6.2.
-/

namespace ResidueAPN

open Polynomial Finset

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Taylor expansion to second order. -/
theorem taylor_diff (G : R[X]) (x δ : R) :
    ∃ c : R, G.eval (x + δ) - G.eval x = δ * ((derivative G).eval x + c * δ) := by
  obtain ⟨c, hc⟩ := Polynomial.binomExpansion G x δ
  exact ⟨c, by rw [hc]; ring⟩

theorem eval_map_hom (π : R →+* F) (G : R[X]) (x : R) : π (G.eval x) = (G.map π).eval (π x) := by
  rw [eval_map, eval₂_hom]

/-- **Key step.** If `π δ = 0` and the reduced derivative does not vanish at `π x`, then
`G(x + δ) = G(x)` forces `δ = 0`. -/
theorem eq_zero_of_eval_add_eq (π : R →+* F) (hunit : ∀ u, π u ≠ 0 → IsUnit u) (G : R[X]) {x δ : R}
    (hδ : π δ = 0) (hder : (derivative (G.map π)).eval (π x) ≠ 0)
    (h : G.eval (x + δ) = G.eval x) : δ = 0 := by
  obtain ⟨c, hc⟩ := taylor_diff G x δ
  have hu : IsUnit ((derivative G).eval x + c * δ) := by
    apply hunit
    rw [map_add, map_mul, hδ, mul_zero, add_zero, eval_map_hom, ← derivative_map]
    exact hder
  rw [h, sub_self] at hc
  exact (hu.mul_left_eq_zero).mp hc.symm

/-- **Proposition 6.1.** Every coefficient lift of a permutation with zero-free derivative permutes `R`. -/
theorem prop_6_1 (π : R →+* F) (hunit : ∀ u, π u ≠ 0 → IsUnit u) (G : R[X])
    (hbij : Function.Bijective (fun t : F => (G.map π).eval t))
    (hder : ∀ t : F, (derivative (G.map π)).eval t ≠ 0) :
    Function.Bijective (fun x : R => G.eval x) := by
  rw [← Finite.injective_iff_bijective]
  intro x y hxy
  simp only at hxy
  have hπ : π x = π y := hbij.1 (by simp only; rw [← eval_map_hom, ← eval_map_hom, hxy])
  have hδ : π (y - x) = 0 := by rw [map_sub, hπ, sub_self]
  have := eq_zero_of_eval_add_eq π hunit G hδ (hder (π x)) (by rw [add_sub_cancel, hxy])
  exact (sub_eq_zero.mp this).symm

/-- Fibres of a surjective ring hom all have the size of the kernel. -/
theorem card_fibre (π : R →+* F) (hsurj : Function.Surjective π) (t : F) :
    (univ.filter (fun x : R => π x = t)).card = (univ.filter (fun x : R => π x = 0)).card := by
  obtain ⟨x0, rfl⟩ := hsurj t
  refine card_bij (fun x _ => x - x0) ?_ ?_ ?_
  · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; rw [map_sub, hx, sub_self]
  · intro a _ b _ h; simpa using h
  · intro y hy; simp only [mem_filter, mem_univ, true_and] at hy
    exact ⟨y + x0, by simp [hy], by ring⟩

/-- `#R = #F · #(ker π)`. -/
theorem card_ker_mul (π : R →+* F) (hsurj : Function.Surjective π) :
    Fintype.card R = Fintype.card F * (univ.filter (fun x : R => π x = 0)).card := by
  have h := card_eq_sum_card_fiberwise (f := fun x : R => π x) (s := univ) (t := univ) (fun _ _ => mem_univ _)
  rw [sum_congr rfl (fun t _ => card_fibre π hsurj t), sum_const, smul_eq_mul, card_univ, card_univ] at h
  exact h

section Unit


/-- On the fibre over a root `t` of the reduction there is exactly one root of `D`, provided the
reduced derivative is nonzero at `t`. -/
theorem card_roots_in_fibre (π : R →+* F) (hsurj : Function.Surjective π)
    (hunit : ∀ u, π u ≠ 0 → IsUnit u) (D : R[X]) (t : F) (hd : (D.map π).eval t = 0)
    (hd' : (derivative (D.map π)).eval t ≠ 0) :
    (univ.filter (fun x : R => π x = t ∧ D.eval x = 0)).card = 1 := by
  set Fib := univ.filter (fun x : R => π x = t)
  set Ker := univ.filter (fun x : R => π x = 0)
  have hmaps : ∀ x ∈ Fib, D.eval x ∈ Ker := by
    intro x hx; simp only [Fib, Ker, mem_filter, mem_univ, true_and] at hx ⊢
    rw [eval_map_hom, hx, hd]
  have hinj : Set.InjOn (fun x => D.eval x) Fib := by
    intro x hx y hy hxy
    simp only [Fib, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    have hδ : π (y - x) = 0 := by rw [map_sub, hx, hy, sub_self]
    have := eq_zero_of_eval_add_eq π hunit D hδ (by rw [hx]; exact hd')
      (by simp only at hxy; rw [add_sub_cancel, hxy])
    exact (sub_eq_zero.mp this).symm
  have hcard : (Fib.image (fun x => D.eval x)).card = Ker.card := by
    rw [card_image_of_injOn hinj]; exact card_fibre π hsurj t
  have himg : Fib.image (fun x => D.eval x) = Ker :=
    eq_of_subset_of_card_le (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy; exact hmaps x hx) hcard.ge
  have h0 : (0 : R) ∈ Ker := by simp [Ker]
  rw [← himg] at h0
  obtain ⟨x0, hx0, hx0e⟩ := mem_image.mp h0
  rw [card_eq_one]
  refine ⟨x0, ?_⟩
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hx, hxe⟩
    exact hinj (by simp [Fib, hx]) hx0 (by simp only; rw [hxe, hx0e])
  · rintro rfl
    simp only [Fib, mem_filter, mem_univ, true_and] at hx0
    exact ⟨hx0, hx0e⟩

/-- **Theorem 6.2(1)** (unit directions off `ker K`). -/
theorem thm_6_2_unit (π : R →+* F) (hsurj : Function.Surjective π)
    (hunit : ∀ u, π u ≠ 0 → IsUnit u) (G : R[X]) (α β : R)
    (hK : ∀ t : F, (derivative (G.map π)).eval (t + π α) - (derivative (G.map π)).eval t ≠ 0) :
    (univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)).card
      = (univ.filter (fun t : F => (G.map π).eval (t + π α) - (G.map π).eval t = π β)).card := by
  set D : R[X] := G.comp (X + C α) - G - C β
  have hDe : ∀ x, D.eval x = G.eval (x + α) - G.eval x - β := by
    intro x; simp [D, eval_comp]
  have hDm : D.map π = (G.map π).comp (X + C (π α)) - G.map π - C (π β) := by
    simp [D, Polynomial.map_sub, map_comp]
  have hdm : ∀ t, (D.map π).eval t = (G.map π).eval (t + π α) - (G.map π).eval t - π β := by
    intro t; rw [hDm]; simp [eval_comp]
  have hdm' : ∀ t, (derivative (D.map π)).eval t
      = (derivative (G.map π)).eval (t + π α) - (derivative (G.map π)).eval t := by
    intro t; rw [hDm]; simp [derivative_comp, eval_comp]
  have hL : univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)
      = univ.filter (fun x : R => D.eval x = 0) := by
    ext x; simp [hDe, sub_eq_zero]
  rw [hL, card_eq_sum_card_fiberwise (f := fun x : R => π x) (t := univ) (fun _ _ => mem_univ _)]
  have hfib : ∀ t ∈ (univ : Finset F),
      ((univ.filter (fun x : R => D.eval x = 0)).filter (fun x => π x = t)).card
        = if (D.map π).eval t = 0 then 1 else 0 := by
    intro t _
    split_ifs with h
    · rw [← card_roots_in_fibre π hsurj hunit D t h (by rw [hdm']; exact hK t), filter_filter]
      congr 1; ext x; simp [and_comm]
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro x hx hxt
      simp only [mem_filter, mem_univ, true_and] at hx
      apply h; rw [← hxt, ← eval_map_hom, hx, map_zero]
  rw [sum_congr rfl hfib, sum_boole]
  apply congrArg Finset.card; ext t; simp [hdm, sub_eq_zero]

end Unit

section Top


/-- **Theorem 6.2(2)** (top ideal). -/
theorem thm_6_2_top (π : R →+* F) (hsurj : Function.Surjective π) (G : R[X]) (α β : R) (hann : ∀ r, α * r = 0 ↔ π r = 0) (hα0 : π α = 0)
    (hfib2 : ∀ s : F, (univ.filter (fun t : F => (derivative (G.map π)).eval t
      = (derivative (G.map π)).eval s)).card = 2)
    (hne : (univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)).Nonempty) :
    (univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)).card
      = 2 * (univ.filter (fun x : R => π x = 0)).card := by
  have hαα : α * α = 0 := (hann α).mpr hα0
  have hdiff : ∀ x, G.eval (x + α) - G.eval x = α * (derivative G).eval x := by
    intro x
    obtain ⟨c, hc⟩ := taylor_diff G x α
    rw [hc, mul_add, ← mul_assoc, mul_comm α c, mul_assoc, hαα, mul_zero, add_zero]
  obtain ⟨x0, hx0⟩ := hne
  simp only [mem_filter, mem_univ, true_and] at hx0
  set S := univ.filter (fun t : F => (derivative (G.map π)).eval t = (derivative (G.map π)).eval (π x0))
  have hset : univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)
      = univ.filter (fun x : R => π x ∈ S) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, S, hdiff, ← hx0]
    rw [← sub_eq_zero, ← mul_sub, hann, map_sub, sub_eq_zero, eval_map_hom, eval_map_hom,
      derivative_map]
  have hsum := card_eq_sum_card_fiberwise (s := univ.filter (fun x : R => π x ∈ S)) (t := S)
    (f := fun x : R => π x) (fun x hx => (mem_filter.mp hx).2)
  rw [hset, hsum]
  have : ∀ t ∈ S, ((univ.filter (fun x : R => π x ∈ S)).filter (fun x => π x = t)).card
      = (univ.filter (fun x : R => π x = 0)).card := by
    intro t ht
    rw [← card_fibre π hsurj t, filter_filter]
    apply congrArg Finset.card; ext x; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨h ▸ ht, h⟩
  rw [sum_congr rfl this, sum_const, smul_eq_mul, hfib2]

end Top

end ResidueAPN
