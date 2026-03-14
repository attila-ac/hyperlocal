/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyConvolutionDischargeFromWcStencil.lean
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcRouteAStencilZero
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport
open Hyperlocal.Cancellation

theorem row0Sigma_wc_eq_zero_fromWcStencil
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    row0Sigma s (wc s) = 0 := by
  rw [row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)]
  exact
    wc_convCoeff3_clean
      (s := s)
      (hStencil := routeA_stencil_zero
        (s := s)
        (hroute := hroute))

end XiPacket
end Targets
end Hyperlocal
