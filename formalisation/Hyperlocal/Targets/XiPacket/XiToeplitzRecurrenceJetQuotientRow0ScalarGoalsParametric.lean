import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeFromWcStencil
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SigmaFromRec2_Parametric
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators

variable [XiJetQuotRec2AtOrderTrueAnalytic]
variable [TAC.XiJetWindowEqAtOrderQuotProvider]
variable [XiAtOrderSigmaProvider]
variable [XiAtOrderCoords01Provider]
variable [RouteAWcScalarProvider]

noncomputable def xiJetQuot_row0_scalarGoals_parametric
    (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s where
  hw0 := by
    exact row0Sigma_w0_eq_zero_fromRec2_parametric (s := s)
  hwc := by
    exact row0Sigma_wc_eq_zero_fromWcStencil (s := s)
  hwp2 := by
    exact row0Sigma_wp2_eq_zero_fromRec2_parametric (s := s)
  hwp3 := by
    exact row0Sigma_wp3_eq_zero_fromRec2_parametric (s := s)

end XiPacket
end Targets
end Hyperlocal
