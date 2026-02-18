import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizToRow0ConvolutionRev
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open Complex
open scoped BigOperators

namespace JetQuotOp

theorem row0Conv_w0 (s : OffSeed Xi) : Row0ConvolutionAtRev s (s.ρ) (w0 s) := by
  exact row0ConvolutionAtRev_of_JetLeibnizAt
    (s := s) (z := s.ρ) (w := w0 s)
    (xiJetLeibnizAt_w0 (s := s))

theorem row0Conv_wc (s : OffSeed Xi) : Row0ConvolutionAtRev s (1 - s.ρ) (wc s) := by
  exact row0ConvolutionAtRev_of_JetLeibnizAt
    (s := s) (z := (1 - s.ρ)) (w := wc s)
    (xiJetLeibnizAt_wc (s := s))

theorem row0Conv_wp2 (s : OffSeed Xi) :
    Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact row0ConvolutionAtRev_of_JetLeibnizAt
    (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s)
    (xiJetLeibnizAt_wp2 (s := s))

theorem row0Conv_wp3 (s : OffSeed Xi) :
    Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact row0ConvolutionAtRev_of_JetLeibnizAt
    (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s)
    (xiJetLeibnizAt_wp3 (s := s))

end JetQuotOp

theorem row0Sigma_w0_eq_zero (s : OffSeed Xi) : row0Sigma s (w0 s) = 0 := by
  exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s := s) (z := s.ρ) (w := w0 s) (JetQuotOp.row0Conv_w0 s)

theorem row0Sigma_wc_eq_zero (s : OffSeed Xi) : row0Sigma s (wc s) = 0 := by
  exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s := s) (z := (1 - s.ρ)) (w := wc s) (JetQuotOp.row0Conv_wc s)

theorem row0Sigma_wp2_eq_zero (s : OffSeed Xi) : row0Sigma s (wp2 s) = 0 := by
  exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s := s) (z := ((starRingEnd ℂ) s.ρ)) (w := wp2 s) (JetQuotOp.row0Conv_wp2 s)

theorem row0Sigma_wp3_eq_zero (s : OffSeed Xi) : row0Sigma s (wp3 s) = 0 := by
  exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s) (JetQuotOp.row0Conv_wp3 s)

end Hyperlocal.Targets.XiPacket
