import ResidueAPN

/-!
Audit, stage 1 (2026-10-07): Theorem 3.1 and Proposition 5.1 of paper_R5.
Run with `lake env lean audit/AuditStage1.lean` after `lake build` (sorry detection is read from the
build log, not from this file).
1. `theorem_3_1_restated` / `proposition_5_1_restated` restate the final types in full and are proved by
   the library theorems. This is a type-compatibility check: if a library theorem's type no longer matches the
   restatement, this file stops compiling. It does not detect a change in the meaning of a definition that both
   sides use (polP, IsAPN, absTr, rep, ...); that is checked by reading the printed definitions (item 2) against
   the paper in papers/formalization/MEANING_MAP.md. (Wording corrected in session R11, GPT R7-06; the earlier
   wording claimed more.)
2. The definitions used are printed for the meaning audit (papers/formalization/MEANING_MAP.md).
3. Axioms are printed; accepted: propext, Classical.choice, Quot.sound.
-/

open ResidueAPN Polynomial Finset

universe u

theorem theorem_3_1_restated :
    ∀ {F : Type u} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {m r : ℕ},
    Fintype.card F = 2 ^ m → 5 ≤ m → Odd m → 3 ≤ r → r < m → Odd r → Nat.Coprime r m →
    (∀ e, (polP (ZMod 2) m r).coeff e = if e ∈ suppP m r then 1 else 0) ∧
    (suppP m r).card = 3 * r - 2 ∧
    (polP (ZMod 2) m r).natDegree = 3 * 2 ^ (m - 2) ∧
    (polP (ZMod 2) m r).map (ZMod.castHom (dvd_refl 2) F)
      = rep (fun x : F => ((polT F r).eval x ^ 3) ^ (2 ^ (m - 2))) ∧
    (∀ x : F, (polP F m r).eval x = ((polT F r).eval x ^ 3) ^ (2 ^ (m - 2))) ∧
    Function.Bijective (fun x : F => (polP F m r).eval x) ∧
    IsAPN (fun x : F => (polP F m r).eval x) ∧
    derivative (polP (ZMod 2) m r) = polD (ZMod 2) m r ∧
    IsOptimalAPNPerm (fun x : F => (polP F m r).eval x) ∧
    (∀ x y : F, (polD F m r).eval y = (polD F m r).eval x ↔ y = x ∨ y = x + 1) ∧
    univ.image (fun x : F => (polD F m r).eval x) = univ.filter (fun y : F => absTr m (y + 1) = 0) ∧
    polP (ZMod 2) m r + 1 = polD (ZMod 2) m r * polE (ZMod 2) m r ∧
    derivative (polE (ZMod 2) m r) = 1 :=
  @theorem_3_1

theorem proposition_5_1_restated :
    ∀ {m r : ℕ}, 2 ≤ m → ∀ (R : Type u) [CommRing R],
    polP ℤ m r = polD ℤ m r * polE ℤ m r - 1 - 2 * (polY ℤ m + polZ ℤ m) ∧
    (polP ℤ m r).map (Int.castRingHom R)
      = polD R m r * polE R m r - 1 - 2 * (polY R m + polZ R m) :=
  @proposition_5_1

set_option pp.explicit true in
#check @ResidueAPN.theorem_3_1
set_option pp.explicit true in
#check @ResidueAPN.proposition_5_1

#print ResidueAPN.polV
#print ResidueAPN.polW
#print ResidueAPN.polY
#print ResidueAPN.polZ
#print ResidueAPN.polD
#print ResidueAPN.polE
#print ResidueAPN.polP
#print ResidueAPN.polT
#print ResidueAPN.expOf
#print ResidueAPN.idx1
#print ResidueAPN.idx2
#print ResidueAPN.idx3
#print ResidueAPN.idx4
#print ResidueAPN.supportIdx
#print ResidueAPN.suppP
#print ResidueAPN.absTr
#print ResidueAPN.IsDerivOptimal
#print ResidueAPN.IsOptimalAPNPerm
#print ResidueAPN.IsAPN
#print ResidueAPN.deriv
#print ResidueAPN.rep

#print axioms ResidueAPN.theorem_3_1
#print axioms theorem_3_1_restated
#print axioms ResidueAPN.proposition_5_1
#print axioms proposition_5_1_restated
#print axioms ResidueAPN.lift_reduces
