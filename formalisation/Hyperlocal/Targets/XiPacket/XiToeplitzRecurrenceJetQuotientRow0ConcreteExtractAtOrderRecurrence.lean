/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderRecurrence.lean

  Reduce the remaining semantic endpoint to the exact Route--C Row--0 Cauchy/convolution gate.

  IMPORTANT: This file must stay cycle-safe.
  Therefore it must NOT import any module that (directly or indirectly) imports
  the AtOrder heart/frontier chain (which imports this file).

  Net effect:
  the only remaining semantic insertion for Task A is exactly the minimal
  Cauchy-product statement you ultimately want to prove from the analytic layer.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderScalarize
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Minimal analytic recurrence output at order `m` (Route--C gate):
Row--0 reverse-Cauchy coefficient vanishes for each AtOrder window.

This is the true semantic content you ultimately need to prove from the analytic layer.
-/
structure XiJetQuotRow0AtOrderConvolutionOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : Row0ConvolutionAtRev s (s.ρ) (w0At m s)
  hwp2At : Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s)
  hwp3At : Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

/--
Task A1 (DAG-safe): build the bundled Route--C gate as a theorem.

This file contains **no axioms**. The proof uses the already discharged
`Row0ConvolutionAtRev` facts for the three AtOrder windows.
-/
theorem xiJetQuotRow0AtOrderConvolutionOut_theorem
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderConvolutionOut m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact row0ConvolutionAtRev_w0At (m := m) (s := s)
  · exact row0ConvolutionAtRev_wp2At (m := m) (s := s)
  · exact row0ConvolutionAtRev_wp3At (m := m) (s := s)

/--
Concrete (scalar) order-`m` jet-quotient recurrence extraction output.

DEF-level (Lean 4.23): derived from the minimal convolution gate above.
-/
noncomputable def xiJetQuotRow0ScalarGoalsAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ScalarGoalsAtOrder m s := by
  classical
  have H : XiJetQuotRow0AtOrderConvolutionOut m s :=
    xiJetQuotRow0AtOrderConvolutionOut_theorem (m := m) (s := s)

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

/--
Type-level AtOrder row--0 concrete extraction witness derived from the scalar recurrence output.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s :=
  extractAtOrder_of_scalarGoals (m := m) (s := s)
    (xiJetQuotRow0ScalarGoalsAtOrder_fromRecurrence (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
