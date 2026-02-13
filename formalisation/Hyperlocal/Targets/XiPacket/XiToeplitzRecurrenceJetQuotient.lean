/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotient.lean

  Route B (jet-quotient) semantic facade.

  Current status:
  * The EllOut statements are now theorem-level, sourced from the operator layer
    (see `XiToeplitzRecurrenceJetQuotientEllFromOperator.lean`).
  * From EllOut we derive the Window-3 Toeplitz row stencils via
    `exists_toeplitzRow3_of_ell_eq_zero`.

  Remaining semantic cliff (for later): the operator layer must eventually
  discharge its single semantic stub `xiJetQuotRow0Out` (now localized).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllToStencil
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientEllFromOperator
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- Route-B semantic target (theorem level, sourced from the operator layer): p=2 EllOut. -/
theorem xiJetQuotEll_spec2 (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 :=
by
  simpa using (xiJetQuotEllOut_fromOperator2 (s := s))

/-- Route-B semantic target (theorem level, sourced from the operator layer): p=3 EllOut. -/
theorem xiJetQuotEll_spec3 (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 :=
by
  simpa using (xiJetQuotEllOut_fromOperator3 (s := s))

/-- Derived (theorem-level) stencil spec for p=2 from EllOut. -/
theorem xiJetQuotStencil_spec2 (s : Hyperlocal.OffSeed Xi) :
  ∃ c2 : Fin 3 → ℝ,
    c2 ≠ 0 ∧
    toeplitzRow3 c2 (reVec3 (w0 s)) ∧
    toeplitzRow3 c2 (reVec3 (wc s)) ∧
    toeplitzRow3 c2 (reVec3 (wp2 s)) := by
  refine
    exists_toeplitzRow3_of_ell_eq_zero
      (u0 := reVec3 (w0 s))
      (uc := reVec3 (wc s))
      (v  := reVec3 (wp2 s))
      (hell := xiJetQuotEll_spec2 (s := s))

/-- Derived (theorem-level) stencil spec for p=3 from EllOut. -/
theorem xiJetQuotStencil_spec3 (s : Hyperlocal.OffSeed Xi) :
  ∃ c3 : Fin 3 → ℝ,
    c3 ≠ 0 ∧
    toeplitzRow3 c3 (reVec3 (w0 s)) ∧
    toeplitzRow3 c3 (reVec3 (wc s)) ∧
    toeplitzRow3 c3 (reVec3 (wp3 s)) := by
  refine
    exists_toeplitzRow3_of_ell_eq_zero
      (u0 := reVec3 (w0 s))
      (uc := reVec3 (wc s))
      (v  := reVec3 (wp3 s))
      (hell := xiJetQuotEll_spec3 (s := s))

end Hyperlocal.Targets.XiPacket
