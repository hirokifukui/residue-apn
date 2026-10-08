import ResidueAPN

/-!
Audit, stage 2 (2026-10-07): Theorem 4.1 (algebraic core), Proposition 6.1, Theorem 6.2 (abstract finite local
ring), Proposition 7.1 of paper_R5. Same conventions as AuditStage1.lean (which still applies to Theorem 3.1 and
Proposition 5.1): the restatements check type compatibility only; the meaning of the definitions is checked by
reading (MEANING_MAP.md). Run with `lake env lean audit/AuditStage2.lean` after `lake build`.
-/

open ResidueAPN Polynomial Finset

universe u v

theorem thmB_core_restated :
    ∀ {m r : ℕ}, 3 ≤ r → r < m → Odd r → Nat.Coprime r m →
    derivative (polP (ZMod 2) m r) = polG (ZMod 2) (m - r) ^ (2 ^ (r - 2)) ∧
    polP (ZMod 2) m r + 1 = polG (ZMod 2) (m - r) ^ (2 ^ (r - 2)) * polE (ZMod 2) m r ∧
    (polG (ZMod 2) (m - r)).Separable ∧
    Fintype.card ((polG (ZMod 2) (m - r)).rootSet (AlgebraicClosure (ZMod 2))) = 2 ^ (m - r) ∧
    IsCoprime (polG (ZMod 2) (m - r)) (polE (ZMod 2) m r) :=
  fun hr hrm hrodd hcop =>
    ⟨derivative_polP_eq_pow hr hrm, polP_add_one_eq_pow (by omega) hrm, separable_polG (by omega),
     card_roots_polG (by omega), isCoprime_polG_polE (by omega) hrm hrodd hcop⟩

theorem thmB_roots_restated :
    ∀ {K : Type u} [Field K] [CharP K 2] {m r : ℕ}, 3 ≤ r → r < m → Odd m → Odd r → Nat.Coprime r m →
    ∀ {α : K}, (polG K (m - r)).eval α = 0 →
      α ^ (2 ^ (2 * (m - r))) = α ∧ α ^ (2 ^ (m - r)) ≠ α ∧ α ^ (2 ^ m) ≠ α ∧
      (polP K m r).eval α = 1 ∧
      rootMultiplicity α (polP K m r + 1) = 2 ^ (r - 2) ∧
      rootMultiplicity α (derivative (polP K m r)) = 2 ^ (r - 2) := by
  intro K _ _ m r hr hrm hmodd hrodd hcop α h
  have hc : Nat.Coprime (2 * (m - r)) m :=
    Nat.Coprime.mul (Nat.coprime_two_left.mpr hmodd)
      ((Nat.coprime_self_sub_left hrm.le).mpr hcop)
  obtain ⟨h1, h2, h3⟩ := multiplicity_at_root hr hrm hrodd hcop h
  exact ⟨root_fixed_two_s h, root_not_fixed_s h, root_not_fixed_of_coprime hc h, h1, h2, h3⟩

#check @ResidueAPN.prop_6_1
#check @ResidueAPN.thm_6_2_unit
#check @ResidueAPN.thm_6_2_top
#check @ResidueAPN.card_ker_mul
#check @ResidueAPN.prop_6_1_family
#check @ResidueAPN.thm_6_2_unit_family
#check @ResidueAPN.thm_6_2_top_family
#check @ResidueAPN.propW
#check @ResidueAPN.det_B_ne_zero
set_option pp.explicit true in
#check @ResidueAPN.thm_6_2_top_family
set_option pp.explicit true in
#check @ResidueAPN.propW

#print ResidueAPN.polG
#print ResidueAPN.IsBit

#print axioms thmB_core_restated
#print axioms thmB_roots_restated
#print axioms ResidueAPN.prop_6_1_family
#print axioms ResidueAPN.thm_6_2_unit_family
#print axioms ResidueAPN.thm_6_2_top_family
#print axioms ResidueAPN.card_ker_mul
#print axioms ResidueAPN.propW
#print axioms ResidueAPN.det_B_ne_zero
#print axioms ResidueAPN.theorem_3_1
#print axioms ResidueAPN.proposition_5_1
