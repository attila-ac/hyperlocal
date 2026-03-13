/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyConvolutionDischargeFromWcStencil.lean
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcRouteAStencilZero
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt

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
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    row0Sigma s (wc s) = 0 := by
  rw [row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)]
  exact
    wc_convCoeff3_clean
      (s := s)
      (hStencil := routeA_stencil_zero (s := s))

end XiPacket
end Targets
end Hyperlocal
