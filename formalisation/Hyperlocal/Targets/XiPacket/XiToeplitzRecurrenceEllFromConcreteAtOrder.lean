/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrder.lean

  Public wrapper for AtOrder ell-out.

  2026-03-13 honest post-axiom state:
  * the upstream proof is now theorem-gated
  * therefore this wrapper can no longer remain assumption-free
  * it must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-- Route--B “AtOrder” ℓ-output (theorem-level; proof is upstream). -/
theorem xiToeplitzEllOutAt_fromRecurrenceC
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiToeplitzEllOutAt m s :=
  xiToeplitzEllOutAt_fromRecurrenceC_proof (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
