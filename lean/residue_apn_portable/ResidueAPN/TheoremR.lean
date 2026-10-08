import ResidueAPN.Ring
import ResidueAPN.TheoremA

/-!
# Proposition 6.1 and Theorem 6.2 for the family `P_{m,r}`

`G ∈ R[X]` is any coefficient lift of `P_{m,r}`: `G.map π = polP F m r`. `R`, `π`, `hunit`, `hann` as in
`ResidueAPN/Ring.lean` (abstract finite local ring; `GR(2^k, m)` is the intended instance, not constructed here).
For `P_{m,r}`, `ker K = {0, 1}` (`ρ = 1`).
-/

namespace ResidueAPN

open Polynomial Finset

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Proposition 6.1 for `P_{m,r}`.** Every coefficient lift permutes `R`. -/
theorem prop_6_1_family {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hmodd : Odd m)
    (hr : 3 ≤ r) (hrm : r < m) (hrodd : Odd r) (hcop : Nat.Coprime r m)
    (π : R →+* F) (hunit : ∀ u, π u ≠ 0 → IsUnit u) (G : R[X]) (hG : G.map π = polP F m r) :
    Function.Bijective (fun x : R => G.eval x) := by
  refine prop_6_1 π hunit G ?_ ?_
  · rw [hG]; exact bijective_evalP hcard hm5 hmodd hr hrodd hcop
  · intro t; rw [hG, derivative_polP hr (by omega)]; exact evalD_ne_zero hcard hm5 hmodd hr t

/-- **Theorem 6.2(1) for `P_{m,r}`.** For `π α ∉ {0, 1}` the ring row equals the residue row, and every
entry is at most `2`. -/
theorem thm_6_2_unit_family {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m) (hmodd : Odd m)
    (hr : 3 ≤ r) (hrm : r < m) (hrodd : Odd r) (hcop : Nat.Coprime r m)
    (π : R →+* F) (hsurj : Function.Surjective π) (hunit : ∀ u, π u ≠ 0 → IsUnit u)
    (G : R[X]) (hG : G.map π = polP F m r) (α β : R) (ha0 : π α ≠ 0) (ha1 : π α ≠ 1) :
    (univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)).card
      = (univ.filter (fun t : F => (polP F m r).eval (t + π α) - (polP F m r).eval t = π β)).card ∧
    (univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)).card ≤ 2 := by
  have hK : ∀ t : F, (derivative (G.map π)).eval (t + π α) - (derivative (G.map π)).eval t ≠ 0 := by
    intro t h
    rw [hG, derivative_polP hr (by omega), sub_eq_zero] at h
    rcases (evalD_eq_iff hcard hm5 hr hcop t (t + π α)).mp h with h' | h'
    · exact ha0 (by linear_combination h')
    · exact ha1 (by linear_combination h')
  have e := thm_6_2_unit π hsurj hunit G α β hK
  rw [hG] at e
  refine ⟨e, ?_⟩
  rw [e]
  have hapn := isAPN_evalP (F := F) hcard hm5 hmodd hr hrodd hcop (π α) ha0 (π β)
  refine le_trans (le_of_eq (congrArg Finset.card ?_)) hapn
  ext t
  simp only [mem_filter, mem_univ, true_and, deriv]
  constructor
  · intro h; linear_combination h + (polP F m r).eval t * (CharTwo.two_eq_zero : (2 : F) = 0)
  · intro h; linear_combination h - (polP F m r).eval t * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- **Theorem 6.2(2) for `P_{m,r}`.** In a top-ideal direction every nonzero entry is `2 · #(ker π)`
(`= 2 q^(k-1)` when `#R = q^k`, by `card_ker_mul`). -/
theorem thm_6_2_top_family {m r : ℕ} (hcard : Fintype.card F = 2 ^ m) (hm5 : 5 ≤ m)
    (hr : 3 ≤ r) (hcop : Nat.Coprime r m)
    (π : R →+* F) (hsurj : Function.Surjective π) (G : R[X]) (hG : G.map π = polP F m r) (α β : R)
    (hann : ∀ r, α * r = 0 ↔ π r = 0) (hα0 : π α = 0)
    (hne : (univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)).Nonempty) :
    (univ.filter (fun x : R => G.eval (x + α) - G.eval x = β)).card
      = 2 * (univ.filter (fun x : R => π x = 0)).card := by
  refine thm_6_2_top π hsurj G α β hann hα0 ?_ hne
  intro s; rw [hG, derivative_polP hr (by omega)]; exact evalD_fibre_card hcard hm5 hr hcop s

end ResidueAPN
