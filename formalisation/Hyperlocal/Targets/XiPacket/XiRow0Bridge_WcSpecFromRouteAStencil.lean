import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeFromWcStencil
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

theorem xiJetQuot_row0_wc_fromStencil
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    row0Sigma s (wc s) = 0 := by
  simpa using row0Sigma_wc_eq_zero_fromWcStencil (s := s)

end XiPacket
end Targets
end Hyperlocal
