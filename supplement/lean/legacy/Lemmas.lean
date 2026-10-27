import Mathlib

/-!
# APN2 R03 — first-stage formal lemmas (Claude, 2026-10-25)

L1 `Drho_surj`      : D_ρ h = h(·+ρ) + h maps onto ρ-periodic functions (ρ ≠ 0, ρ+ρ = 0; values in a group of exponent 2).
L2 `quad_fiber`     : in a field of characteristic 2 with μ ≠ 0, μy²+Ay = μz²+Az ↔ z = y ∨ z = y + A/μ.
L3 `coset_dichotomy`: c+H and c+E+H coincide if E ∈ H and are disjoint otherwise.
L4 `absTr_artin_schreier` : in a finite field of order 2^m, Tr(t²+t) = 0 for Tr x = Σ_{i<m} x^(2^i).

These are abstract lemmas.  They are NOT a formalization of the Galois-ring theorems (mod 8 stability,
spectra, minimax); see the correspondence table in LEAN_REPORT_R03.md.
-/

namespace APN2R03

open Finset

section L1
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

/-- The pair relation `b = a ∨ b = a + ρ` (an equivalence since ρ + ρ = 0). -/
def pairSetoid (ρ : G) (hρ2 : ρ + ρ = 0) : Setoid G where
  r a b := b = a ∨ b = a + ρ
  iseqv := by
    refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
    · rintro a b (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, add_assoc, hρ2, add_zero])
    · rintro a b c (h1 | h1) (h2 | h2)
      · exact Or.inl (by rw [h2, h1])
      · exact Or.inr (by rw [h2, h1])
      · exact Or.inr (by rw [h2, h1])
      · exact Or.inl (by rw [h2, h1, add_assoc, hρ2, add_zero])

theorem Drho_surj (ρ : G) (hρ : ρ ≠ 0) (hρ2 : ρ + ρ = 0)
    (f : G → M) (hf : ∀ a, f (a + ρ) = f a) :
    ∃ h : G → M, ∀ a, h (a + ρ) + h a = f a := by
  classical
  letI : Setoid G := pairSetoid ρ hρ2
  let out : G → G := fun a => (⟦a⟧ : Quotient (pairSetoid ρ hρ2)).out
  have hout : ∀ a, out a = a ∨ out a = a + ρ := by
    intro a
    have h : a = out a ∨ a = out a + ρ := Quotient.mk_out a
    rcases h with h | h
    · exact Or.inl h.symm
    · right
      calc out a = out a + ρ + ρ := by rw [add_assoc, hρ2, add_zero]
        _ = a + ρ := by rw [← h]
  have hshift : ∀ a, out (a + ρ) = out a := by
    intro a
    have hq : (⟦a + ρ⟧ : Quotient (pairSetoid ρ hρ2)) = ⟦a⟧ :=
      Quotient.sound (show a = a + ρ ∨ a = a + ρ + ρ from
        Or.inr (by rw [add_assoc, hρ2, add_zero]))
    simp only [out, hq]
  have hne : ∀ a : G, a + ρ ≠ a := by
    intro a h
    apply hρ
    have := congrArg (fun x => x - a) h
    simpa using this
  refine ⟨fun a => if out a = a then f a else 0, ?_⟩
  intro a
  rcases hout a with h1 | h1
  · have h2 : ¬ (out (a + ρ) = a + ρ) := by
      rw [hshift, h1]; exact fun h => hne a h.symm
    show (if out (a + ρ) = a + ρ then f (a + ρ) else 0) + (if out a = a then f a else 0) = f a
    rw [if_neg h2, if_pos h1, zero_add]
  · have h2 : out (a + ρ) = a + ρ := by rw [hshift, h1]
    have h3 : ¬ (out a = a) := by rw [h1]; exact hne a
    show (if out (a + ρ) = a + ρ then f (a + ρ) else 0) + (if out a = a then f a else 0) = f a
    rw [if_pos h2, if_neg h3, add_zero, hf]

end L1

section L2
variable {F : Type*} [Field F] [CharP F 2]

theorem quad_fiber (μ A y z : F) (hμ : μ ≠ 0) :
    μ * y ^ 2 + A * y = μ * z ^ 2 + A * z ↔ z = y ∨ z = y + A / μ := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hd : μ * (A / μ) = A := by field_simp
  constructor
  · intro h
    have h2 : (z - y) * (μ * (z + y) + A) = 0 := by linear_combination (-1 : F) * h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; exact sub_eq_zero.mp h3
    · right
      have h4 : z + y = A / μ := by
        rw [eq_div_iff hμ]
        linear_combination h3 - (A) * two
      linear_combination h4 - y * two
  · rintro (h | h)
    · rw [h]
    · rw [h]
      linear_combination (-(A / μ)) * hd + (-((A / μ) * (μ * y + A))) * two

end L2

section L3

theorem coset_dichotomy {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (c E x : G) :
    (E ∈ H → (x - c ∈ H ↔ x - (c + E) ∈ H)) ∧
    (E ∉ H → ¬ (x - c ∈ H ∧ x - (c + E) ∈ H)) := by
  have key : x - (c + E) = (x - c) - E := by abel
  refine ⟨fun hE => ?_, fun hE h => ?_⟩
  · rw [key]
    constructor
    · intro h; exact H.sub_mem h hE
    · intro h
      have := H.add_mem h hE
      simpa using this
  · apply hE
    have h2 : (x - c) - E ∈ H := key ▸ h.2
    have := H.sub_mem h.1 h2
    simpa using this

end L3

section L4
variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

/-- The absolute trace written as a sum of Frobenius powers. -/
def absTr (m : ℕ) (x : K) : K := ∑ i ∈ range m, x ^ (2 ^ i)

theorem absTr_artin_schreier (m : ℕ) (hcard : Fintype.card K = 2 ^ m) (t : K) :
    absTr m (t ^ 2 + t) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold absTr
  have hfrob : ∀ i : ℕ, (t ^ 2 + t) ^ (2 ^ i) = t ^ (2 ^ (i + 1)) + t ^ (2 ^ i) := by
    intro i
    rw [add_pow_char_pow, ← pow_mul, ← pow_succ']
  simp_rw [hfrob]
  have tele : ∀ n : ℕ, ∑ i ∈ range n, (t ^ (2 ^ (i + 1)) + t ^ (2 ^ i)) = t ^ (2 ^ n) + t := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, pow_one]
      linear_combination (-t) * two
    | succ n ih =>
      rw [sum_range_succ, ih]
      linear_combination (t ^ (2 ^ n)) * two
  rw [tele, ← hcard, FiniteField.pow_card]
  linear_combination t * two

end L4

end APN2R03

#print axioms APN2R03.Drho_surj
#print axioms APN2R03.quad_fiber
#print axioms APN2R03.coset_dichotomy
#print axioms APN2R03.absTr_artin_schreier
