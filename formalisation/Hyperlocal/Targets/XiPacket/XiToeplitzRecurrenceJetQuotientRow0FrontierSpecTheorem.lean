/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpecTheorem.lean

  Theorem-backed version of the Row0 frontier `wc` spec fact.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

variable [XiJetQuotRec2AtOrderTrueAnalytic]
variable [XiAtOrderSigmaProvider]
variable [XiAtOrderCoords01Provider]
variable [TAC.XiJetWindowEqAtOrderQuotProvider]
variable [RouteAWcScalarProvider]

theorem xiJetQuot_row0_wc_spec_theorem
  (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using xiJetQuot_row0_wc_spec_proof (s := s)

theorem xiJetQuot_row0_wc_spec' (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) =
    0 :=
  xiJetQuot_row0_wc_spec_theorem (s := s)

end XiPacket
end Targets
end Hyperlocal
