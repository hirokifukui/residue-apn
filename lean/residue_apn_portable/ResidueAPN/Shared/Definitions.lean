-- Copied from ~/lean/apnlift/APNLift/Core/Definitions.lean (apnlift, H. Fukui; sha256 9046c194dec24068…)
-- on 2026-10-07; only the namespace APNLift -> ResidueAPN and the import path were changed.
import Mathlib

/-!
# APNLift core definitions

Stage 1 (R21 / C4-13): the point of this file today is to fix the environment and show that
`lake build` really passes.  Only definitions and statements that are certain are written here;
nothing is asserted about mathlib API that has not been compiled.

Specification: `specification/theorems.md`, entries S1-S10.
-/

namespace ResidueAPN

variable {F : Type*} [Field F]

/-- The polar form of `Q`:  `B_Q(a,x) = Q(a+x) + Q(a) + Q(x) + Q(0)`.
Specification entry S2. -/
def polar (Q : F -> F) (a x : F) : F :=
  Q (a + x) + Q a + Q x + Q 0

/-- The polar form is symmetric in its two arguments.  This is the fact that makes
`T_Q = { x => B_Q(b,x) }` a space of admissible corrections (spec S7). -/
theorem polar_comm (Q : F -> F) (a x : F) : polar Q a x = polar Q x a := by
  unfold polar
  rw [add_comm a x]
  ring

/-- `Q` is quadratic when its polar form is additive in the second argument.
Stated, not yet used: the correspondence with Boolean degree at most two is a separate
obligation (spec S2) and is not assumed anywhere. -/
def IsQuadratic (Q : F -> F) : Prop :=
  forall a x y : F, polar Q a (x + y) = polar Q a x + polar Q a y

end ResidueAPN
