/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WcScalarToToeplitzRow0Core.lean

  Parametric core from the Route-A scalar identity directly to the row-0 wc goals.

  This file lives above the cycle:
    Route-A scalar identity
      -> wc coeff-3 zero
      -> row0Sigma wc = 0
      -> Toeplitz row-0 wc frontier fact

  When the final independent scalar theorem lands, the last seam kill will be a
  one-line application of the theorem exposed here.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3WcRouteANormalForm
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeCore
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation
open Hyperlocal.Transport

theorem row0Sigma_wc_eq_zero_of_routeA_scalar_core
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    row0Sigma s (wc s) = 0 := by
  exact
    row0Sigma_wc_eq_zero_of_coeff3
      (s := s)
      (h3 := row0ConvCoeff3_wc_of_routeA_scalar (s := s) (hroute := hroute))

theorem toeplitz_row0_wc_eq_zero_of_routeA_scalar_core
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  exact
    toeplitz_row0_wc_eq_zero_of_coeff3
      (s := s)
      (h3 := row0ConvCoeff3_wc_of_routeA_scalar (s := s) (hroute := hroute))

end XiPacket
end Targets
end Hyperlocal
