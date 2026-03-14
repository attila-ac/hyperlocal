/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WcSigma2DeltaToToeplitzRow0Core.lean

  Final above-cycle insertion point for the last seam:

      σ2 = 2*delta
        -> wc coeff-3 zero
        -> row0Sigma wc = 0
        -> toeplitz row-0 wc frontier fact

  Once the quartet algebra provides `σ2 = 2*delta`, the seam kill is a one-line
  application of the theorem exposed here.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcScalarClosedForm
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
open Hyperlocal.Transport
open Hyperlocal.Cancellation

theorem row0Sigma_wc_eq_zero_of_sigma2_eq_two_delta
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ : JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    row0Sigma s (wc s) = 0 := by
  exact
    row0Sigma_wc_eq_zero_of_coeff3
      (s := s)
      (h3 := row0ConvCoeff3_wc_eq_zero_of_sigma2_eq_two_delta
        (s := s) (hσ2δ := hσ2δ))

theorem toeplitz_row0_wc_eq_zero_of_sigma2_eq_two_delta
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ : JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  exact
    toeplitz_row0_eq_zero_of_row0Sigma_eq_zero
      (s := s)
      (w := wc s)
      (row0Sigma_wc_eq_zero_of_sigma2_eq_two_delta
        (s := s) (hσ2δ := hσ2δ))

end XiPacket
end Targets
end Hyperlocal
