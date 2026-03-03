/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceInject.lean

  Boundary module (semantic cliff isolation).

  This file used to be an axiom boundary exporting the two bCoeff phase-lock facts
  at primes 2 and 3.

  R2 cleanup: those facts are now theorem-level, via the order-0 Toeplitz identity
  path packaged in `XiToeplitzRecurrenceIdentity.lean`.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentity
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAt0NonzeroInject

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-- Semantic injection: recurrence forces `bCoeff(2)=0` (theorem-level). -/
theorem xiToeplitz_hb2_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  -- The identity lemma is packaged in the `p : ℝ` + `{2,3}` disjunction form.
  simpa using
    (xiToeplitzRecurrenceIdentity_p (s := s) (p := (2 : ℝ)) (Or.inl rfl))

/-- Semantic injection: recurrence forces `bCoeff(3)=0` (theorem-level). -/
theorem xiToeplitz_hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  simpa using
    (xiToeplitzRecurrenceIdentity_p (s := s) (p := (3 : ℝ)) (Or.inr rfl))

end XiPacket
end Targets
end Hyperlocal
