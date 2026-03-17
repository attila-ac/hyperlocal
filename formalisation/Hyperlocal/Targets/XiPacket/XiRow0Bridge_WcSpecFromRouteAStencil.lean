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

/--
Honest theorem-level wc row-0 closure from the Route-A scalar stencil.

This is not closed from typeclass assumptions alone: the current source theorem
still requires the explicit scalar seam hypothesis `hroute`.
-/
theorem xiJetQuot_row0_wc_fromStencil
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    row0Sigma s (wc s) = 0 := by
  simpa using row0Sigma_wc_eq_zero_fromWcStencil
    (s := s)
    (hroute := hroute)

#print axioms xiJetQuot_row0_wc_fromStencil

end XiPacket
end Targets
end Hyperlocal
