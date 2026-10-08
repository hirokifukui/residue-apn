import ResidueAPN.ThmAImage

/-!
# Proposition 7.1 (W) of paper_R5 — two words, two layers

Setting (after the normalisation stated before Proposition 7.1, which is kept as a hypothesis here):
`p : F → F` with `Tr(p(y+1) + p(y)) = 1` for every `y`. `a, b` distinct, nonzero, of trace `0`;
`B = [[a, b], [b, a+b]]` (rows), `M = B⁻¹`.

* `det_B_ne_zero`: `det B = a(a+b) − b² ≠ 0` for odd `m`, so `M` exists.
* `propW`: if `α = (α₁, α₂) ∈ {0,1}²` (entries in `{0,1} ⊆ F`), `β_i = p(x_i + α_i) + p(x_i)` and
  `γ ∈ {0,1}² \ {0}`, then `β ≠ Bγ`; i.e. `Mβ ∉ {0,1}² \ {0}`. (The proof uses only the first word;
  in particular the conclusion holds for every `α ∈ {0,1}²`, nonzero or not.)
-/

namespace ResidueAPN

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Elements `0` or `1`. -/
def IsBit (u : F) : Prop := u = 0 ∨ u = 1

theorem det_B_ne_zero {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (hodd : Odd m) {a b : F} (ha : a ≠ 0) :
    a * (a + b) - b * b ≠ 0 := by
  intro h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hq : a ^ 2 + a * b + b ^ 2 = 0 := by linear_combination h + b ^ 2 * h2
  set t := b * a⁻¹ with ht_def
  have ht : t ^ 2 + t + 1 = 0 := by
    have e : t ^ 2 + t + 1 = (a ^ 2 + a * b + b ^ 2) * (a⁻¹) ^ 2 := by
      rw [ht_def]; field_simp; ring
    rw [e, hq, zero_mul]
  have h3 : t ^ 3 = (1 : F) ^ 3 := by linear_combination (t - 1) * ht
  have h1 : t = 1 := cube_injective hcard hodd h3
  rw [h1] at ht
  exact one_ne_zero (by linear_combination ht - h2)

theorem propW {m : ℕ} {p : F → F} (htr : ∀ y, absTr m (p (y + 1) + p y) = 1)
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hta : absTr m a = 0) (htb : absTr m b = 0)
    (x₁ x₂ α₁ α₂ : F) (hα₁ : IsBit α₁) (_hα₂ : IsBit α₂)
    (γ₁ γ₂ : F) (hγ₁ : IsBit γ₁) (hγ₂ : IsBit γ₂) (hγ : ¬ (γ₁ = 0 ∧ γ₂ = 0)) :
    ¬ (p (x₁ + α₁) + p x₁ = a * γ₁ + b * γ₂ ∧ p (x₂ + α₂) + p x₂ = b * γ₁ + (a + b) * γ₂) := by
  rintro ⟨h₁, _⟩
  -- the first entry of Bγ is a nonzero element of trace 0
  have hab0 : a + b ≠ 0 := fun h => hab (CharTwo.add_eq_zero.mp h)
  have key : a * γ₁ + b * γ₂ ≠ 0 ∧ absTr m (a * γ₁ + b * γ₂) = 0 := by
    rcases hγ₁ with rfl | rfl <;> rcases hγ₂ with rfl | rfl
    · exact absurd ⟨rfl, rfl⟩ hγ
    · simp only [mul_zero, zero_add, mul_one]; exact ⟨hb, htb⟩
    · simp only [mul_one, mul_zero, add_zero]; exact ⟨ha, hta⟩
    · simp only [mul_one]; exact ⟨hab0, by rw [absTr_add, hta, htb, add_zero]⟩
  rcases hα₁ with rfl | rfl
  · rw [add_zero, CharTwo.add_self_eq_zero] at h₁
    exact key.1 h₁.symm
  · have := htr x₁
    rw [h₁, key.2] at this
    exact zero_ne_one this

end ResidueAPN
