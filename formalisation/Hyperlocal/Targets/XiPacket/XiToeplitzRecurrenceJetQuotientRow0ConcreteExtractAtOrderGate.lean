/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGate.lean

  Cycle-safe gate for AtOrder concrete extraction:
  provides exactly the minimal Route--C Row--0 convolution output as an axiom,
  and derives the scalar goals + concrete extraction witness.

  IMPORTANT:
  This file must NOT import any *outer* AtOrder frontier modules.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderScalarize
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-- Route--C gate (Row--0 reverse convolution) for each AtOrder window. -/
structure XiJetQuotRow0AtOrderConvolutionOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : Row0ConvolutionAtRev s (s.ρ) (w0At m s)
  hwp2At : Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s)
  hwp3At : Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

/-- Single semantic insertion point (cycle-safe). -/
axiom xiJetQuotRow0AtOrderConvolutionOut_axiom
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderConvolutionOut m s

theorem xiJetQuotRow0AtOrderConvolutionOut
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderConvolutionOut m s := by
  exact xiJetQuotRow0AtOrderConvolutionOut_axiom (m := m) (s := s)

/-- Scalar goals derived from the convolution gate. -/
noncomputable def xiJetQuotRow0ScalarGoalsAtOrder_fromGate
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ScalarGoalsAtOrder m s := by
  classical
  have H := xiJetQuotRow0AtOrderConvolutionOut (m := m) (s := s)
  refine ⟨?_, ?_, ?_⟩
  ·
    exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := s.ρ) (w := w0At m s) H.hw0At
  ·
    exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) H.hwp2At
  ·
    exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) H.hwp3At

/-- Concrete extraction witness derived from the scalar goals. -/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromGate
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s :=
  extractAtOrder_of_scalarGoals (m := m) (s := s)
    (xiJetQuotRow0ScalarGoalsAtOrder_fromGate (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
