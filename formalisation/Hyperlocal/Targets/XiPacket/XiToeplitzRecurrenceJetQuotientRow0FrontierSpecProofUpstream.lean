/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream.lean

  Upstream proof for the Row0 frontier `wc` spec fact.

  POLICY:
  * do NOT use the scalar-goals witness route here anymore
  * consume the parallel theorem-side concrete `wc` producer directly
  * this file is allowed to be theorem-gated
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

variable [XiJetQuotRec2AtOrderTrueAnalytic]
variable [XiAtOrderSigmaProvider]
variable [XiAtOrderCoords01Provider]
variable [TAC.XiJetWindowEqAtOrderQuotProvider]
variable [RouteAWcScalarProvider]

theorem xiJetQuot_row0_wc_spec_proof (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using xiJetQuot_row0_wc_fromWcStencil (s := s)

end XiPacket
end Targets
end Hyperlocal
