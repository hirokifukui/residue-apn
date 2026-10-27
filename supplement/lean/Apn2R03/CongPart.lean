import Mathlib

/-!
# The residue-class partition of polynomial key-alternating rounds (Claude, 2026-10-25, R05-08)

Rounds `x ↦ M (S x) + κ` on `Fin n → R`, where `S` applies a polynomial `F ∈ R[X]` to each word,
`M` is any additive map (in particular any `R`-linear layer) and `κ` is added in `R`.
If two states agree modulo 2 word by word, so do their images, for every key: polynomial maps
satisfy `(x - y) ∣ F(x) - F(y)`, additive maps preserve `2 ∣ ·`, and key addition cancels.
An initial whitening key changes nothing.  The relation does not involve unit differences in
an essential way, so it is outside the scope of the per-S-box unit-direction bounds; it is the
reason why a complete cipher needs a component that breaks the residue partition.

* `poly_cong`  : 2 ∣ x − y → 2 ∣ F(x) − F(y)
* `round_cong` : the relation is preserved by one round
* `iter_cong`  : … and by any number of rounds after a whitening key, for every key schedule
-/

namespace APN2.CongPart

open Polynomial

variable {R : Type*} [CommRing R]

theorem poly_cong (F : R[X]) (x y : R) (h : (2 : R) ∣ x - y) : (2 : R) ∣ F.eval x - F.eval y :=
  dvd_trans h (Polynomial.sub_dvd_eval_sub x y F)

variable {n : ℕ}

/-- two states agree modulo 2 in every word -/
def cong2 (x y : Fin n → R) : Prop := ∀ j, (2 : R) ∣ x j - y j

/-- one round: wordwise polynomial S-box, additive linear layer, key addition in R -/
def round (F : R[X]) (M : (Fin n → R) →+ (Fin n → R)) (κ : Fin n → R) (x : Fin n → R) : Fin n → R :=
  M (fun j => F.eval (x j)) + κ

theorem round_cong (F : R[X]) (M : (Fin n → R) →+ (Fin n → R)) (κ x y : Fin n → R)
    (h : cong2 x y) : cong2 (round F M κ x) (round F M κ y) := by
  have hs : ∀ j, (2 : R) ∣ F.eval (x j) - F.eval (y j) := fun j => poly_cong F _ _ (h j)
  choose w hw using hs
  have hdiff : (fun j => F.eval (x j)) - (fun j => F.eval (y j)) = w + w := by
    funext j; simp only [Pi.sub_apply, Pi.add_apply]; rw [hw j]; ring
  have e : round F M κ x - round F M κ y = M w + M w := by
    unfold round
    rw [add_sub_add_right_eq_sub, ← map_sub, hdiff, map_add]
  intro j
  refine ⟨M w j, ?_⟩
  have := congrFun e j
  simp only [Pi.sub_apply, Pi.add_apply] at this
  rw [this]; ring

/-- whitening key κ 0, then rounds with keys κ 1, κ 2, … -/
def iter (F : R[X]) (M : (Fin n → R) →+ (Fin n → R)) (κ : ℕ → Fin n → R) :
    ℕ → (Fin n → R) → (Fin n → R)
  | 0, x => x + κ 0
  | N + 1, x => round F M (κ (N + 1)) (iter F M κ N x)

theorem iter_cong (F : R[X]) (M : (Fin n → R) →+ (Fin n → R)) (κ : ℕ → Fin n → R)
    (x y : Fin n → R) (h : cong2 x y) : ∀ N, cong2 (iter F M κ N x) (iter F M κ N y) := by
  intro N
  induction N with
  | zero =>
    intro j
    simp only [iter, Pi.add_apply, add_sub_add_right_eq_sub]
    exact h j
  | succ N ih => exact round_cong F M (κ (N + 1)) _ _ ih

end APN2.CongPart

#print axioms APN2.CongPart.poly_cong
#print axioms APN2.CongPart.round_cong
#print axioms APN2.CongPart.iter_cong
