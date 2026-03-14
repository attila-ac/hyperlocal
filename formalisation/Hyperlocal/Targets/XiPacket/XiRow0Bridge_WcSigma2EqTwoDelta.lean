/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WcSigma2EqTwoDelta.lean

  Honest reduction layer for the final algebra kill.

  This file does NOT yet prove the final theorem
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ).
  Instead it gives the exact above-cycle reductions:

      Route-A scalar zero -> σ2 = 2*delta
      wc coeff-3 zero     -> σ2 = 2*delta

  So once either independent producer is proved, the final theorem is a one-line wrapper.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcScalarClosedForm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

theorem sigma2_eq_two_delta_of_routeA_scalar_zero
    (s : OffSeed Xi)
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  have hz : JetQuotOp.σ2 s - (2 : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
    calc
      JetQuotOp.σ2 s - (2 : ℂ) * (XiTransport.delta s : ℂ)
          =
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
            symm
            exact routeA_stencil_wc_closedForm (s := s)
      _ = 0 := hroute
  exact sub_eq_zero.mp hz

theorem sigma2_eq_two_delta_of_row0ConvCoeff3_wc_zero
    (s : OffSeed Xi)
    [RouteAWcScalarProvider]
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  have hz : JetQuotOp.σ2 s - (2 : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
    calc
      JetQuotOp.σ2 s - (2 : ℂ) * (XiTransport.delta s : ℂ)
          = convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 := by
              symm
              exact row0ConvCoeff3_wc_closedForm (s := s)
      _   = 0 := h3
  exact sub_eq_zero.mp hz

/--
Final wrapper to use once the independent scalar theorem is available.
Paste the real producer into `hroute`.
-/
theorem sigma2_eq_two_delta
    (s : OffSeed Xi)
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  exact sigma2_eq_two_delta_of_routeA_scalar_zero (s := s) (hroute := hroute)

end XiPacket
end Targets
end Hyperlocal
