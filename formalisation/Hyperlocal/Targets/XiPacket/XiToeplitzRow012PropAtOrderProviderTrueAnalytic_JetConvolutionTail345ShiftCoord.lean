/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345ShiftCoord.lean

  NEXT reduction layer (post Tail345Reductions):

  From the Row012 reverse-stencil convolution hypothesis on a window `w`,
  derive the “shifted row0Sigma” coordinate equations, using:

    * XiRow0Bridge_StencilToShiftedRow0Sigma.lean
        row0Sigma s (shiftWin1 w) = 0
        row0Sigma s (shiftWin2 w) = 0

    * XiRow0Bridge_WindowShiftRow0Sigma.lean
        row0Sigma s (shiftWin1 w) = σ2*s*w2 + (-σ3*s)*w1
        row0Sigma s (shiftWin2 w) = (-σ3*s)*w2

  Output (manuscript-close “A equations”):
    (1) JetQuotOp.σ2 s * w 2 + (-JetQuotOp.σ3 s) * w 1 = 0
    (2) (-JetQuotOp.σ3 s) * w 2 = 0

  Then specialise to the three canonical windows:
    w := w0At m s, wp2At m s, wp3At m s

  This file is sigma/frontier/extractor-free and does not mention `convCoeff`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WindowShiftRow0Sigma
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_StencilToShiftedRow0Sigma
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace Tail345ShiftCoord

/-
  The exact hypothesis type `Row012ConvolutionAtRev` lives in your stencil files.
  We never unfold it here; we only pass it to the existing theorems that already
  know how to consume it.
-/

/-- From the Row012 reverse-stencil hypothesis, get the one-step shifted coordinate equation. -/
theorem sigma_shift1_coord_eq_zero_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    (JetQuotOp.σ2 s) * (w 2) + (-JetQuotOp.σ3 s) * (w 1) = 0 := by
  -- (A) get the shifted-sigma vanishing from the stencil lemma
  have h0 : row0Sigma s (shiftWin1 w) = 0 :=
    row0Sigma_shiftWin1_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H
  -- (B) compute row0Sigma on shiftWin1 and rewrite
  -- row0Sigma_shiftWin1 states: row0Sigma s (shiftWin1 w) = σ2*s*w2 + (-σ3*s)*w1
  -- so the target is just that RHS = 0.
  simpa [row0Sigma_shiftWin1 (s := s) (w := w)] using h0

/-- From the Row012 reverse-stencil hypothesis, get the two-step shifted coordinate equation. -/
theorem sigma_shift2_coord_eq_zero_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    (-JetQuotOp.σ3 s) * (w 2) = 0 := by
  -- (A) get the shifted-sigma vanishing from the stencil lemma
  have h0 : row0Sigma s (shiftWin2 w) = 0 :=
    row0Sigma_shiftWin2_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H
  -- (B) compute row0Sigma on shiftWin2 and rewrite
  simpa [row0Sigma_shiftWin2 (s := s) (w := w)] using h0

/-!
### Canonical-window specialisations
-/

theorem sigma_shift1_coord_eq_zero_w0At
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    (H : Row012ConvolutionAtRev s z (w0At m s)) :
    (JetQuotOp.σ2 s) * ((w0At m s) 2) + (-JetQuotOp.σ3 s) * ((w0At m s) 1) = 0 :=
  sigma_shift1_coord_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w0At m s) H

theorem sigma_shift2_coord_eq_zero_w0At
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    (H : Row012ConvolutionAtRev s z (w0At m s)) :
    (-JetQuotOp.σ3 s) * ((w0At m s) 2) = 0 :=
  sigma_shift2_coord_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := w0At m s) H

theorem sigma_shift1_coord_eq_zero_wp2At
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    (H : Row012ConvolutionAtRev s z (wp2At m s)) :
    (JetQuotOp.σ2 s) * ((wp2At m s) 2) + (-JetQuotOp.σ3 s) * ((wp2At m s) 1) = 0 :=
  sigma_shift1_coord_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := wp2At m s) H

theorem sigma_shift2_coord_eq_zero_wp2At
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    (H : Row012ConvolutionAtRev s z (wp2At m s)) :
    (-JetQuotOp.σ3 s) * ((wp2At m s) 2) = 0 :=
  sigma_shift2_coord_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := wp2At m s) H

theorem sigma_shift1_coord_eq_zero_wp3At
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    (H : Row012ConvolutionAtRev s z (wp3At m s)) :
    (JetQuotOp.σ2 s) * ((wp3At m s) 2) + (-JetQuotOp.σ3 s) * ((wp3At m s) 1) = 0 :=
  sigma_shift1_coord_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := wp3At m s) H

theorem sigma_shift2_coord_eq_zero_wp3At
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    (H : Row012ConvolutionAtRev s z (wp3At m s)) :
    (-JetQuotOp.σ3 s) * ((wp3At m s) 2) = 0 :=
  sigma_shift2_coord_eq_zero_of_row012ConvolutionAtRev (s := s) (z := z) (w := wp3At m s) H

end Tail345ShiftCoord

end XiPacket
end Targets
end Hyperlocal
