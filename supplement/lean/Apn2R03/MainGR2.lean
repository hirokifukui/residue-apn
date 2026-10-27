import Apn2R03.MainGR
import Apn2R03.ResAPN

/-!
# Theorem A on GR(2^k, m), all unit directions, no hypothesis (Claude, 2026-10-25, R04-09)

With the residue APN property now proved (`resAPN3`, `resAPN5`), the unit-direction statement of
Theorem A holds on the concrete Galois rings without the input `hAPN`:
every entry δ_{F♯}(α, β) with α a unit is ≤ 2q, and ≤ 2 off the exceptional direction ρ = 1.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial

section main
variable (k : ℕ) (hk : 3 ≤ k) (f : (ZMod (2 ^ k))[X]) (hf : f.Monic)
variable [Fact (Irreducible (fbar k hk f))]
variable [Fintype (AdjoinRoot f)] [DecidableEq (AdjoinRoot f)]
variable [Fintype (AdjoinRoot (fbar k hk f))] [DecidableEq (AdjoinRoot (fbar k hk f))]

/-- **Theorem A (r = 3) on GR(2^k, m), all unit directions.** -/
theorem thmA3_GR_units (m : ℕ) (hdeg : f.natDegree = m) (hm5 : 5 ≤ m) (hodd : Odd m)
    (h3 : Nat.Coprime 3 m) (α β : AdjoinRoot f) (hα : (grs k hk f hf).π α ≠ 0) :
    GRS.delta (Fsh3 (AdjoinRoot f) m) α β ≤ 2 * Fintype.card (AdjoinRoot (fbar k hk f)) ∧
      ((grs k hk f hf).π α ≠ 1 → GRS.delta (Fsh3 (AdjoinRoot f) m) α β ≤ 2) := by
  obtain ⟨hc, hK⟩ := grs_card k hk f hf
  rw [hdeg] at hK
  exact (grs k hk f hf).fam3_units' hc m hm5 hodd hK h3 α β hα

/-- **Theorem A (r ≥ 5) on GR(2^k, m), all unit directions.** -/
theorem thmA5_GR_units (m r : ℕ) (hdeg : f.natDegree = m) (hm5 : 5 ≤ m) (hr5 : 5 ≤ r) (hrm : r < m)
    (hodd : Odd r) (hmodd : Odd m) (hcop : Nat.Coprime r m) (α β : AdjoinRoot f)
    (hα : (grs k hk f hf).π α ≠ 0) :
    GRS.delta (Fsh5 (AdjoinRoot f) m r) α β ≤ 2 * Fintype.card (AdjoinRoot (fbar k hk f)) ∧
      ((grs k hk f hf).π α ≠ 1 → GRS.delta (Fsh5 (AdjoinRoot f) m r) α β ≤ 2) := by
  obtain ⟨hc, hK⟩ := grs_card k hk f hf
  rw [hdeg] at hK
  exact (grs k hk f hf).fam5_units' hc m r hm5 hr5 hrm hodd hmodd hK hcop α β hα

end main

end APN2

#print axioms APN2.thmA3_GR_units
#print axioms APN2.thmA5_GR_units
