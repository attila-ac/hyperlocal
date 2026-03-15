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
Closed stencil consequence of a closed `wc` row-0 sigma fact.
-/
theorem routeA_stencil_zero_of_row0Sigma_wc_zero
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma : row0Sigma s (wc s) = 0) :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  exact routeA_stencil_zero_fromRecurrence
    (s := s)
    (hrec := routeA_recurrence_at_one_sub_rho_of_row0Sigma_wc
      (s := s)
      (hsigma := hsigma))

/--
Closed coeff-3 consequence of a closed `wc` row-0 sigma fact.

Placed here, not in `XiRow0Bridge_WcCoeff3RouteAStencil.lean`, to avoid the cycle

  WcCoeff3RouteAStencil
    -> WcRouteAStencilZero
    -> RouteARecurrenceAtOneSubRhoFromWcSigma
    -> WcCoeff3RouteAStencil.
-/
theorem wc_convCoeff3_clean_of_row0Sigma_wc_zero
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma : row0Sigma s (wc s) = 0) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  exact wc_convCoeff3_clean_of_routeA_stencil
    (s := s)
    (hStencil := routeA_stencil_zero_of_row0Sigma_wc_zero
      (s := s)
      (hsigma := hsigma))

/--
Legacy wrapper, still theorem-gated on the current public seam.
-/
theorem routeA_stencil_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  exact routeA_stencil_zero_fromRecurrence
    (s := s)
    (hrec := routeA_recurrence_at_one_sub_rho_from_row0Frontier_wc
      (s := s)
      (hroute := hroute))

end XiPacket
end Targets
end Hyperlocal
