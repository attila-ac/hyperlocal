import Hyperlocal.Targets.XiPacket.XiRow0Bridge_RouteARecurrenceAtOneSubRhoFromWcSigma
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_RouteAStencilFromRecurrence

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
Route-A stencil identity, now theorem-backed from the Route-A recurrence.

Note:
the current recurrence wrapper `routeA_recurrence_at_one_sub_rho_from_row0Frontier_wc`
already depends only on the thin public `wc` frontier seam, so this theorem no longer
needs the extra `XiJetQuotRec2AtOrderTrueAnalytic` gate here.
-/
theorem routeA_stencil_zero
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  exact routeA_stencil_zero_fromRecurrence
    (s := s)
    (hrec := routeA_recurrence_at_one_sub_rho_from_row0Frontier_wc (s := s))

end XiPacket
end Targets
end Hyperlocal
