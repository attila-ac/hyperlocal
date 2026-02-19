/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGate.lean

  Cycle-safe gate for AtOrder concrete extraction:
  provides exactly one semantic insertion point (as a theorem wrapper),
  and derives scalar goals + concrete extraction witness.

  CHANGE (fixes unknown identifier issues downstream):
    The Gate structure is now defined in the defs-only module
      `...GateDefs.lean`
    so that analytic discharge files can import it without importing the Gate axiom.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderScalarize
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateFromAnalytic

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-
Single semantic insertion point.

Currently defined by forwarding to the analytic-discharge theorem in
`...GateFromAnalytic.lean`.

When you replace
  `xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic`
by the true recurrence extraction theorem, this Gate becomes axiom-free
without changing downstream code.
-/
theorem xiJetQuotRow0AtOrderConvolutionOut_axiom
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderConvolutionOut m s := by
  exact xiJetQuotRow0AtOrderConvolutionOut_fromAnalytic (m := m) (s := s)

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
