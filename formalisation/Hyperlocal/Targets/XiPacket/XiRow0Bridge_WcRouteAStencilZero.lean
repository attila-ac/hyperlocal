/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WcRouteAStencilZero.lean

  Final local insertion point for the remaining `wc` coeff-3 seam.

  Policy:
  * do NOT re-enter frontier specs
  * do NOT use `JetLeibnizAt_wc` here; that is the wrong battlefield
  * this file should prove the Route-A scalar stencil zero theorem directly from
    the actual Route-A scalar mathematics / manuscript theorem once identified
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcCoeff3RouteAStencil
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3WcRouteANormalForm

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
Exact remaining mathematical target.

This should be discharged from the Route-A scalar theory once the correct
upstream theorem is identified.
-/
theorem wc_routeA_stencil_zero
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
      + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
      - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  sorry

theorem wc_convCoeff3_clean
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  exact row0ConvCoeff3_wc_of_routeA_scalar
    (s := s)
    (wc_routeA_stencil_zero (s := s))

end XiPacket
end Targets
end Hyperlocal
