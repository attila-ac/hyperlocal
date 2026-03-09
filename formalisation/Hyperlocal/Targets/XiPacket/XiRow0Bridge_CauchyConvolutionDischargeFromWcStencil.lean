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

/--
Parallel theorem-side `wc` sigma discharge from the new Route-A stencil proof.

This does NOT touch the historical `row0Sigma_wc_eq_zero`.
It is a sibling theorem intended for downstream retargeting.
-/
theorem row0Sigma_wc_eq_zero_fromWcStencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    row0Sigma s (wc s) = 0 := by
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)] using
    (wc_convCoeff3_clean
      (s := s)
      (hStencil := routeA_stencil_zero (s := s)))

end XiPacket
end Targets
end Hyperlocal
