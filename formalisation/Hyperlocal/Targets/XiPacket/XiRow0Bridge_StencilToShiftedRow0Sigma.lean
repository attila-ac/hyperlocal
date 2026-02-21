/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_StencilToShiftedRow0Sigma.lean

  Task 1 (2026-02-20):
    Prove the missing glue

      Row012ConvolutionAtRev s z w
        ⇒ row0Sigma s (shiftWin1 w) = 0
        ⇒ row0Sigma s (shiftWin2 w) = 0

  Design constraints:
    * cycle-safe, algebra only
    * no new axioms

  Strategy:
    Use the existing stencil-to-coordinate equalities to show w0=w1=w2=0,
    then evaluate `row0Sigma` on the shifted windows via the existing
    `row0Sigma_shiftWin1/2` computations.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyStencilToCoordEq
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WindowShiftRow0Sigma
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- From the row012 stencil, derive `w 1 = 0`. -/
theorem w1_eq_zero_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    w 1 = 0 := by
  classical
  have hw0 : w 0 = 0 :=
    w0_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H
  have h4 : (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0 :=
    (coordEqs_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H).2.1
  have h4' : (-2 : ℂ) * (w 1) = 0 := by
    simpa [hw0] using h4
  have hne : (-2 : ℂ) ≠ 0 := by
    norm_num
  exact (mul_eq_zero.mp h4').resolve_left hne

/-- From the row012 stencil, derive `w 2 = 0`. -/
theorem w2_eq_zero_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    w 2 = 0 := by
  classical
  have hw0 : w 0 = 0 :=
    w0_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H
  have hw1 : w 1 = 0 :=
    w1_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H
  have hSigma : row0Sigma s w = 0 :=
    (coordEqs_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H).1
  have hSigma' : (-(2 : ℂ)) * (w 2) = 0 := by
    -- `row0Sigma s w = (-2)*w2 + σ2*w1 + (-σ3)*w0`
    simpa [row0Sigma, hw0, hw1] using hSigma
  have hne : (-(2 : ℂ)) ≠ 0 := by
    norm_num
  exact (mul_eq_zero.mp hSigma').resolve_left hne

/-- Task 1 (part A): the row012 stencil forces the one-step-shifted row0Sigma to vanish. -/
theorem row0Sigma_shiftWin1_eq_zero_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    row0Sigma s (shiftWin1 w) = 0 := by
  classical
  have hw1 : w 1 = 0 :=
    w1_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H
  have hw2 : w 2 = 0 :=
    w2_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H
  -- Evaluate `row0Sigma` on the shifted window.
  simpa [row0Sigma_shiftWin1 (s := s) (w := w), hw1, hw2]

/-- Task 1 (part B): the row012 stencil forces the two-step-shifted row0Sigma to vanish. -/
theorem row0Sigma_shiftWin2_eq_zero_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    row0Sigma s (shiftWin2 w) = 0 := by
  classical
  have hw2 : w 2 = 0 :=
    w2_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H
  simpa [row0Sigma_shiftWin2 (s := s) (w := w), hw2]

/-- Convenience bundling for downstream: both shifted-row0Sigma vanishings at once. -/
theorem row0Sigma_shiftWin12_eq_zero_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    row0Sigma s (shiftWin1 w) = 0 ∧ row0Sigma s (shiftWin2 w) = 0 := by
  exact ⟨
    row0Sigma_shiftWin1_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H,
    row0Sigma_shiftWin2_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H⟩

namespace StencilToShiftedRow0SigmaExport
export _root_.Hyperlocal.Targets.XiPacket
  (w1_eq_zero_of_row012ConvolutionAtRev
   w2_eq_zero_of_row012ConvolutionAtRev
   row0Sigma_shiftWin1_eq_zero_of_row012ConvolutionAtRev
   row0Sigma_shiftWin2_eq_zero_of_row012ConvolutionAtRev
   row0Sigma_shiftWin12_eq_zero_of_row012ConvolutionAtRev)
end StencilToShiftedRow0SigmaExport

end XiPacket
end Targets
end Hyperlocal
