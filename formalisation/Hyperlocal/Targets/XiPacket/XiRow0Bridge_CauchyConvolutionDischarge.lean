/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyConvolutionDischarge.lean

  Route-C discharge of the row-0 scalar sigma goals.

  The new core file
    `XiRow0Bridge_CauchyConvolutionDischargeCore.lean`
  exposes a direct parametric insertion point for the `wc` branch:
  abstract coeff-3 proof in, sigma/toeplitz row-0 fact out.

  This wrapper preserves the current downstream surface by feeding in the
  existing semantic theorem for coeff-3.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizToRow0ConvolutionRev
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeCore
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3Semantic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open Complex
open scoped BigOperators

variable [XiJetQuotRec2AtOrderTrueAnalytic]
variable [TAC.XiJetWindowEqAtOrderQuotProvider]
variable [RouteAWcScalarProvider]

namespace JetQuotOp

theorem row0Conv_w0 (s : OffSeed Xi) : Row0ConvolutionAtRev s (s.ρ) (w0 s) := by
  simpa using (row0ConvolutionAtRev_w0 (s := s))

theorem row0Conv_wc (s : OffSeed Xi) : Row0ConvolutionAtRev s (1 - s.ρ) (wc s) := by
  simpa using (row0ConvolutionAtRev_wc (s := s))

theorem row0Conv_wp2 (s : OffSeed Xi) :
    Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  simpa using (row0ConvolutionAtRev_wp2 (s := s))

theorem row0Conv_wp3 (s : OffSeed Xi) :
    Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  simpa using (row0ConvolutionAtRev_wp3 (s := s))

end JetQuotOp

theorem row0Sigma_w0_eq_zero (s : OffSeed Xi) : row0Sigma s (w0 s) = 0 := by
  exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s := s) (z := s.ρ) (w := w0 s) (JetQuotOp.row0Conv_w0 s)

theorem row0Sigma_wc_eq_zero (s : OffSeed Xi) : row0Sigma s (wc s) = 0 := by
  exact row0Sigma_wc_eq_zero_of_coeff3
    (s := s)
    (h3 := row0ConvCoeff3_eq_zero_wc (s := s))

theorem row0Sigma_wp2_eq_zero (s : OffSeed Xi) : row0Sigma s (wp2 s) = 0 := by
  exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s) (JetQuotOp.row0Conv_wp2 s)

theorem row0Sigma_wp3_eq_zero (s : OffSeed Xi) : row0Sigma s (wp3 s) = 0 := by
  exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3 s) (JetQuotOp.row0Conv_wp3 s)

end Hyperlocal.Targets.XiPacket
