/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderRecurrence.lean

  NEXT SURGICAL PUSH (toward discharging Task A):

  Reduce the remaining semantic endpoint to the exact Route--C Row--0 Cauchy/convolution gate.

  Concretely:
  * Keep ONE axiom: `xiJetQuotRow0AtOrderConvolutionOut` (Row0ConvolutionAtRev for each AtOrder window).
  * Derive the three scalar identities `row0Sigma = 0` using
      `row0Sigma_eq_zero_from_Row0ConvolutionAtRev`.
  * Package into `XiJetQuotRow0ScalarGoalsAtOrder`.
  * Derive the Type-level witness via `extractAtOrder_of_scalarGoals`.

  Net effect:
  the only remaining semantic insertion for Task A becomes exactly the minimal
  Cauchy-product statement you ultimately want to prove from the analytic layer.
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
SINGLE semantic endpoint (temporary):
the AtOrder analytic recurrence extraction theorem, stated in the minimal Row--0
Cauchy/convolution form.

Replace this axiom by a theorem once the analytic extraction layer is formalised.
-/
axiom xiJetQuotRow0AtOrderConvolutionOut
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderConvolutionOut m s

/--
Concrete (scalar) order-`m` jet-quotient recurrence extraction output.

DEF-level (Lean 4.23): derived from the minimal convolution gate above.
Once `xiJetQuotRow0AtOrderConvolutionOut` is proved as a theorem, this becomes axiom-free.
-/
noncomputable def xiJetQuotRow0ScalarGoalsAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ScalarGoalsAtOrder m s := by
  classical
  have H : XiJetQuotRow0AtOrderConvolutionOut m s :=
    xiJetQuotRow0AtOrderConvolutionOut (m := m) (s := s)

  refine ⟨?_, ?_, ?_⟩
  ·
    -- w0At
    exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := s.ρ) (w := w0At m s) H.hw0At
  ·
    -- wp2At
    exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) H.hwp2At
  ·
    -- wp3At
    exact row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) H.hwp3At

/--
Type-level AtOrder row--0 concrete extraction witness derived from the scalar recurrence output.

Once the convolution axiom above is replaced by a theorem, this definition becomes axiom-free.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s :=
  extractAtOrder_of_scalarGoals (m := m) (s := s)
    (xiJetQuotRow0ScalarGoalsAtOrder_fromRecurrence (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
