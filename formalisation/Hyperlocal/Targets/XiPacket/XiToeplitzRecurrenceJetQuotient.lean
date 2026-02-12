import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllToStencil
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- Route-B semantic target (temporary axiom; later theorem from the operator): p=2 EllOut. -/
axiom xiJetQuotEll_spec2 (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0

/-- Route-B semantic target (temporary axiom; later theorem from the operator): p=3 EllOut. -/
axiom xiJetQuotEll_spec3 (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0

/-- Derived (theorem-level) stencil spec for p=2 from EllOut via the new reverse bridge. -/
theorem xiJetQuotStencil_spec2 (s : Hyperlocal.OffSeed Xi) :
  ∃ c2 : Fin 3 → ℝ,
    c2 ≠ 0 ∧
    toeplitzRow3 c2 (reVec3 (w0 s)) ∧
    toeplitzRow3 c2 (reVec3 (wc s)) ∧
    toeplitzRow3 c2 (reVec3 (wp2 s)) := by
  simpa using
    exists_toeplitzRow3_of_ell_eq_zero
      (u0 := reVec3 (w0 s))
      (uc := reVec3 (wc s))
      (v  := reVec3 (wp2 s))
      (hell := xiJetQuotEll_spec2 s)

/-- Derived (theorem-level) stencil spec for p=3 from EllOut via the new reverse bridge. -/
theorem xiJetQuotStencil_spec3 (s : Hyperlocal.OffSeed Xi) :
  ∃ c3 : Fin 3 → ℝ,
    c3 ≠ 0 ∧
    toeplitzRow3 c3 (reVec3 (w0 s)) ∧
    toeplitzRow3 c3 (reVec3 (wc s)) ∧
    toeplitzRow3 c3 (reVec3 (wp3 s)) := by
  simpa using
    exists_toeplitzRow3_of_ell_eq_zero
      (u0 := reVec3 (w0 s))
      (uc := reVec3 (wc s))
      (v  := reVec3 (wp3 s))
      (hell := xiJetQuotEll_spec3 s)

-- the rest of the file can stay as-is: xiJetQuotRecOut now consumes theorem-level stencils.

end Hyperlocal.Targets.XiPacket
