import ResidueAPN

/-!
Audit, stage 3 (2026-10-07, session R11): Lemma 2.2 of the paper. Same conventions as AuditStage1.lean: the
restatement checks type compatibility; the meaning of `IsQuadSupp`, `kappaOf`, `linMap`, `c2` and
`IsDerivOptimal` is checked by reading (printed below; MEANING_MAP.md).
-/

open ResidueAPN Polynomial Finset

universe u

theorem lemma_2_2_restated :
    ∀ {F : Type u} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {m : ℕ},
    Fintype.card F = 2 ^ m → Odd m → ∀ {p : (ZMod 2)[X]}, IsQuadSupp m p →
    (IsDerivOptimal (p.map (ZMod.castHom (dvd_refl 2) F)) ↔
      p.coeff 1 = 1 ∧ EuclideanDomain.gcd (kappaOf m p) (X ^ m - 1) = X + 1) :=
  @lemma_2_2

set_option pp.explicit true in
#check @ResidueAPN.lemma_2_2

#print ResidueAPN.IsQuadSupp
#print ResidueAPN.kappaOf
#print ResidueAPN.linMap
#print ResidueAPN.c2
#print ResidueAPN.kerL

#print axioms ResidueAPN.lemma_2_2
#print axioms lemma_2_2_restated
#print axioms ResidueAPN.lemma_2_2_core
#print axioms ResidueAPN.derivative_quadratic
#print axioms ResidueAPN.card_kerL_of_dvd
