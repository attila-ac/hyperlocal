/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcrete.lean

  Collision-free exported non-AtOrder ℓ-output.

  NEW POLICY:
  Do NOT rebuild this through the legacy concrete/minimal-model recurrence corridor.
  The AtOrder proof/export lane is now cleaner. So the non-AtOrder endpoint should be
  obtained by specializing the AtOrder theorem at `m = 0`.

  2026-03-13 honest post-axiom state:
  * the AtOrder theorem is now theorem-gated
  * therefore this non-AtOrder specialization wrapper must expose the same gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-- Project-facing endpoint (collision-free): obtain the non-AtOrder ℓ-output by
specializing the clean AtOrder theorem at `m = 0`. -/
theorem xiToeplitzEllOut_fromRecurrenceC
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiToeplitzEllOut s := by
  let h0 := xiToeplitzEllOutAt_fromRecurrenceC (m := 0) (s := s)
  refine ⟨?_, ?_⟩
  · simpa [w0At_zero (s := s), wp2At_zero (s := s)] using h0.hell2
  · simpa [w0At_zero (s := s), wp3At_zero (s := s)] using h0.hell3

end XiPacket
end Targets
end Hyperlocal
