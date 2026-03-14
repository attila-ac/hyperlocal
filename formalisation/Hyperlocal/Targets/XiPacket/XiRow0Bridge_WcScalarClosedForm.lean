/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WcScalarClosedForm.lean

  Collapse the remaining Route-A `wc` scalar stencil to a pure closed form.

  After the current graph cuts, the last seam burden is no longer an import
  problem. It is the pure scalar identity

      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ).

  This file makes that target explicit.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3WcRouteANormalForm
import Hyperlocal.Targets.XiPacket.XiRouteA_WcNormalization
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

theorem routeA_stencil_wc_closedForm
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
      + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
      - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)
      =
    JetQuotOp.σ2 s - (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  rw [routeA_G_deriv2_at_one_sub_rho (s := s),
      routeA_G_deriv_at_one_sub_rho (s := s),
      routeA_G_at_one_sub_rho (s := s)]
  ring

theorem routeA_stencil_zero_of_sigma2_eq_two_delta
    (s : OffSeed Xi)
    [RouteAWcScalarProvider]
    (hσ2δ : JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
      + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
      - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  rw [routeA_stencil_wc_closedForm (s := s), hσ2δ]
  ring

theorem row0ConvCoeff3_wc_closedForm
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3
      =
    JetQuotOp.σ2 s - (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  rw [row0ConvCoeff3_wc_routeA_normalForm (s := s)]
  exact routeA_stencil_wc_closedForm (s := s)

theorem row0ConvCoeff3_wc_eq_zero_of_sigma2_eq_two_delta
    (s : OffSeed Xi)
    [RouteAWcScalarProvider]
    (hσ2δ : JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  rw [row0ConvCoeff3_wc_closedForm (s := s), hσ2δ]
  ring

end XiPacket
end Targets
end Hyperlocal
