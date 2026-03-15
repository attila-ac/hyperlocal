import Hyperlocal.Cancellation.Recurrence
import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizToRow0ConvolutionRevCore
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0SigmaToToeplitzRow0
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

/-
  Parametric core above the cycle:

    abstract wc coeff-3 proof
      -> Row0ConvolutionAtRev for wc
      -> row0Sigma wc = 0
      -> Toeplitz row-0 wc frontier fact

  This is the direct insertion point for the final independent upstream proof.
-/

theorem row0Sigma_wc_eq_zero_of_coeff3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    row0Sigma s (wc s) = 0 := by
  exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s := s)
    (z := 1 - s.ρ)
    (w := wc s)
    (row0ConvolutionAtRev_wc_of_coeff3 (s := s) (h3 := h3))

theorem toeplitz_row0_wc_eq_zero_of_coeff3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  exact toeplitz_row0_eq_zero_of_row0Sigma_eq_zero
    (s := s)
    (w := wc s)
    (row0Sigma_wc_eq_zero_of_coeff3 (s := s) (h3 := h3))

theorem toeplitz_row0_wc_eq_zero_of_row0Sigma_wc_zero
    (s : OffSeed Xi)
    (hsigma : row0Sigma s (wc s) = 0) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  exact toeplitz_row0_eq_zero_of_row0Sigma_eq_zero
    (s := s)
    (w := wc s)
    hsigma


end XiPacket
end Targets
end Hyperlocal
