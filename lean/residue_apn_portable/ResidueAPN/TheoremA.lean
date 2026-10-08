import ResidueAPN.ThmAImage

/-!
# Theorem 3.1 and Proposition 5.1 of paper_R5 — final statements

`theorem_3_1` bundles items (1)–(4) of Theorem 3.1 for a finite field `F` with `2^m` elements,
`m` odd, `m ≥ 5`, and admissible `r`. The polynomial `P_{m,r}` lives in `(ZMod 2)[X]`;
its image in `F[X]` is `(polP (ZMod 2) m r).map φ` with `φ = ZMod.castHom`, which equals `polP F m r`
(`map_polP`).

`proposition_5_1` is the identity in `ℤ[X]`; by `Polynomial.map` it holds over every
commutative ring, in particular over `GR(2^k, m)`. The operation count of Proposition 5.1 is not
formalized.
-/

namespace ResidueAPN

open Polynomial Finset

/-- **Theorem 3.1 (A).** -/
theorem theorem_3_1 {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {m r : ℕ}
    (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hmodd : Odd m)
    (hr : 3 ≤ r) (hrm : r < m) (hrodd : Odd r) (hcop : Nat.Coprime r m) :
    -- (1) coefficients in 𝔽₂, exactly 3r − 2 terms, degree 3q/4, and P = red((T_r^3)^(2^(m-2)))
    (∀ e, (polP (ZMod 2) m r).coeff e = if e ∈ suppP m r then 1 else 0) ∧
    (suppP m r).card = 3 * r - 2 ∧
    (polP (ZMod 2) m r).natDegree = 3 * 2 ^ (m - 2) ∧
    (polP (ZMod 2) m r).map (ZMod.castHom (dvd_refl 2) F)
      = rep (fun x : F => ((polT F r).eval x ^ 3) ^ (2 ^ (m - 2))) ∧
    -- (2) as a map, P = σ^(m-2) ∘ X^3 ∘ T_r; it is an APN permutation
    (∀ x : F, (polP F m r).eval x = ((polT F r).eval x ^ 3) ^ (2 ^ (m - 2))) ∧
    Function.Bijective (fun x : F => (polP F m r).eval x) ∧
    IsAPN (fun x : F => (polP F m r).eval x) ∧
    -- (3) P' = D, derivative-optimal, fibres {x, x+1}, image 1 + ker Tr
    derivative (polP (ZMod 2) m r) = polD (ZMod 2) m r ∧
    IsOptimalAPNPerm (fun x : F => (polP F m r).eval x) ∧
    (∀ x y : F, (polD F m r).eval y = (polD F m r).eval x ↔ y = x ∨ y = x + 1) ∧
    univ.image (fun x : F => (polD F m r).eval x) = univ.filter (fun y : F => absTr m (y + 1) = 0) ∧
    -- (4) P + 1 = D E in 𝔽₂[X], E' = 1
    polP (ZMod 2) m r + 1 = polD (ZMod 2) m r * polE (ZMod 2) m r ∧
    derivative (polE (ZMod 2) m r) = 1 := by
  refine ⟨coeff_polP hr hrm, card_suppP hr hrm, natDegree_polP hr hrm, ?_,
    eval_polP hcard (by omega) (by omega), bijective_evalP hcard hm5 hmodd hr hrodd hcop,
    isAPN_evalP hcard hm5 hmodd hr hrodd hcop, derivative_polP hr (by omega),
    isOptimalAPNPerm_P hcard hm5 hmodd hr hrm hrodd hcop, evalD_eq_iff hcard hm5 hr hcop,
    image_evalD hcard hm5 hr hcop, polP_add_one (by omega), derivative_polE hr (by omega)⟩
  rw [map_polP]
  refine rep_unique (degree_polP_lt hcard hrm.le (by omega)) (fun x => eval_polP hcard (by omega) (by omega) x)

/-- **Proposition 5.1 (C), the identity.** `P̂ = D̂ Ê − 1 − 2(Ŷ + Ẑ)` in `ℤ[X]`, and the same
identity for the image of the `0/1` lift in any commutative ring `R` (e.g. `GR(2^k, m)`). -/
theorem proposition_5_1 {m r : ℕ} (hm : 2 ≤ m) (R : Type*) [CommRing R] :
    polP ℤ m r = polD ℤ m r * polE ℤ m r - 1 - 2 * (polY ℤ m + polZ ℤ m) ∧
    (polP ℤ m r).map (Int.castRingHom R)
      = polD R m r * polE R m r - 1 - 2 * (polY R m + polZ R m) := by
  refine ⟨polP_eq_int hm, ?_⟩
  rw [map_polP]; exact polP_eq_int hm

/-- The `0/1` lift reduces to `P_{m,r}` modulo 2. -/
theorem lift_reduces {m r : ℕ} : (polP ℤ m r).map (Int.castRingHom (ZMod 2)) = polP (ZMod 2) m r :=
  map_polP _ m r

end ResidueAPN
