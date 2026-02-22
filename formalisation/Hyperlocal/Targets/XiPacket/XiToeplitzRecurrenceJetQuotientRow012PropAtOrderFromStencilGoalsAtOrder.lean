/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromStencilGoalsAtOrder.lean

  Pure algebra bridge (Path A, witness-free):

    XiRow012StencilGoalsAtOrder m s  ==>  XiJetQuotRow012PropAtOrder m s.

  This is cycle-safe and does not touch the extractor/heart stack.
-/

import Hyperlocal.Targets.XiPacket.XiRow012StencilGoalsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff345Algebra
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
open Hyperlocal.Cancellation

private theorem toeplitzRow012Prop_of_stencil_eqs
    (s : OffSeed Xi) (w : Window 3)
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0)
    (h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0)
    (h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0) :
    ToeplitzRow012Prop s w := by
  classical

  -- n=5 ⇒ (-2)*w0 = 0 ⇒ w0 = 0
  have hw0 : w 0 = 0 := by
    have hlin : (-2 : ℂ) * (w 0) = 0 := by
      -- IMPORTANT: use the repo’s actual rewrite lemma name
      simpa [convCoeff5_unfold_eq_lincomb (s := s) (w := w)] using h5
    have hne : (-2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hlin).resolve_left hne

  -- n=4 ⇒ σ2*w0 + (-2)*w1 = 0; with w0=0 ⇒ w1=0
  have hw1 : w 1 = 0 := by
    have hlin : (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0 := by
      simpa [convCoeff4_unfold_eq_lincomb (s := s) (w := w)] using h4
    have hlin' : (-2 : ℂ) * (w 1) = 0 := by
      simpa [hw0] using hlin
    have hne : (-2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hlin').resolve_left hne

  -- n=3 ⇒ row0Sigma=0; with w0=w1=0 ⇒ w2=0
  have hSig : row0Sigma s w = 0 := by
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w)] using h3

  have hw2 : w 2 = 0 := by
    have hlin : (-2 : ℂ) * (w 2) = 0 := by
      simpa [row0Sigma, hw0, hw1, add_assoc, add_left_comm, add_comm] using hSig
    have hne : (-2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hlin).resolve_left hne

  -- shifted sigmas (for Toeplitz rows 1,2)
  have hsh1 : row0Sigma s (shiftWin1 w) = 0 := by
    simpa [row0Sigma_shiftWin1 (s := s) (w := w), hw1, hw2]
  have hsh2 : row0Sigma s (shiftWin2 w) = 0 := by
    simpa [row0Sigma_shiftWin2 (s := s) (w := w), hw2]

  -- convert sigma facts to Toeplitz rows
  have h0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 :=
    toeplitz_row0_eq_zero_of_row0Sigma_eq_zero (s := s) (w := w) hSig
  have h1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0 :=
    toeplitz_row1_eq_zero_of_row0Sigma_shiftWin1_eq_zero (s := s) (w := w) hsh1
  have h2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0 :=
    toeplitz_row2_eq_zero_of_row0Sigma_shiftWin2_eq_zero (s := s) (w := w) hsh2

  exact ⟨h0, h1, h2⟩

/-- AtOrder bundling: stencil goals imply Prop-level Toeplitz Row012 payload. -/
theorem xiJetQuotRow012PropAtOrder_of_stencilGoalsAtOrder
    (m : ℕ) (s : OffSeed Xi)
    (H : XiRow012StencilGoalsAtOrder m s) :
    XiJetQuotRow012PropAtOrder m s := by
  classical
  refine XiJetQuotRow012PropAtOrder.ofProp (m := m) (s := s) ?_ ?_ ?_
  · exact toeplitzRow012Prop_of_stencil_eqs (s := s) (w := w0At m s) H.hw0_3 H.hw0_4 H.hw0_5
  · exact toeplitzRow012Prop_of_stencil_eqs (s := s) (w := wp2At m s) H.hwp2_3 H.hwp2_4 H.hwp2_5
  · exact toeplitzRow012Prop_of_stencil_eqs (s := s) (w := wp3At m s) H.hwp3_3 H.hwp3_4 H.hwp3_5

end XiPacket
end Targets
end Hyperlocal
