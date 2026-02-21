/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionToToeplitzRow012Prop.lean

  Task 2 (2026-02-20): fully algebraic bridge

    Row012ConvolutionAtRev s z w  ⇒  ToeplitzRow012Prop s w.

  This is cycle-safe: it depends only on the row012 stencil + shift-to-Toeplitz bridges.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyStencilToCoordEq
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_StencilToShiftedRow0Sigma
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0SigmaToToeplitzRow0
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0SigmaShiftToToeplitzRow12

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Row012 reverse-stencil implies Prop-level Toeplitz rows 0/1/2 vanish for the same window. -/
theorem toeplitzRow012Prop_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    ToeplitzRow012Prop s w := by
  classical

  have hSig : row0Sigma s w = 0 :=
    (coordEqs_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H).1

  have h0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 :=
    toeplitz_row0_eq_zero_of_row0Sigma_eq_zero (s := s) (w := w) hSig

  have hsh1 : row0Sigma s (shiftWin1 w) = 0 :=
    row0Sigma_shiftWin1_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H

  have hsh2 : row0Sigma s (shiftWin2 w) = 0 :=
    row0Sigma_shiftWin2_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H

  have h1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0 :=
    toeplitz_row1_eq_zero_of_row0Sigma_shiftWin1_eq_zero (s := s) (w := w) hsh1

  have h2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0 :=
    toeplitz_row2_eq_zero_of_row0Sigma_shiftWin2_eq_zero (s := s) (w := w) hsh2

  exact ⟨h0, h1, h2⟩

namespace Row012ConvolutionToToeplitzRow012PropExport
export _root_.Hyperlocal.Targets.XiPacket (toeplitzRow012Prop_of_row012ConvolutionAtRev)
end Row012ConvolutionToToeplitzRow012PropExport

end XiPacket
end Targets
end Hyperlocal
