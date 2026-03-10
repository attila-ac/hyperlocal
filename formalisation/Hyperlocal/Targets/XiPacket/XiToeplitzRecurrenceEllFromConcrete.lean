/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcrete.lean

  Collision-free exported non-AtOrder ℓ-output.

  NEW POLICY:
  Do NOT rebuild this through the legacy concrete/minimal-model recurrence corridor.
  The AtOrder proof/export lane is now cleaner. So the non-AtOrder endpoint should be
  obtained by specializing the AtOrder theorem at `m = 0`.

  This is the exact proof/export seam cut suggested by the second-wave measurement:
  `xiToeplitzEllOutAt_fromRecurrenceC` is already off `xiJetQuot_row0_wc_spec`,
  while `xiToeplitzEllOut_fromRecurrenceC` is not.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

/-- Project-facing endpoint (collision-free): obtain the non-AtOrder ℓ-output by
specializing the clean AtOrder theorem at `m = 0`. -/
theorem xiToeplitzEllOut_fromRecurrenceC (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOut s := by
  let h0 := xiToeplitzEllOutAt_fromRecurrenceC (m := 0) (s := s)
  refine ⟨?_, ?_⟩
  · simpa [w0At_zero (s := s), wp2At_zero (s := s)] using h0.hell2
  · simpa [w0At_zero (s := s), wp3At_zero (s := s)] using h0.hell3

end XiPacket
end Targets
end Hyperlocal
