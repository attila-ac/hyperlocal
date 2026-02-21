/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionFromRow0AndCoords.lean

  Pure algebra, cycle-safe:
    Show convCoeff at n=4,5 in closed form for (row0CoeffSeqRev, winSeqRev),
    and reduce Row012ConvolutionAtRev to Row0ConvolutionAtRev + (w0=0) + (w1=0).

  This does NOT introduce any new axioms.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeAtOrderRow012

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Complex
open Hyperlocal.Cancellation
open Hyperlocal.Transport

/-- Closed form: convCoeff at n=4 for the reverse-padded row0 kernel. -/
theorem convCoeff_row0Rev_eq_n4
    (s : OffSeed Xi) (w : Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4
      = (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) := by
  classical
  -- Expand the finite convolution to a polynomial identity and normalize.
  simp [convCoeff, row0CoeffSeqRev, winSeqRev, Finset.range_succ]
  ring_nf

/-- Closed form: convCoeff at n=5 for the reverse-padded row0 kernel. -/
theorem convCoeff_row0Rev_eq_n5
    (s : OffSeed Xi) (w : Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5
      = (-2 : ℂ) * (w 0) := by
  classical
  simp [convCoeff, row0CoeffSeqRev, winSeqRev, Finset.range_succ]

/--
If you have the minimal Row0 gate (convCoeff 3 = 0) and additionally w0=0 and w1=0,
then you automatically get the row012 stencil gate (coeffs 3,4,5 vanish).
-/
theorem row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_coords
    (s : OffSeed Xi) (z : ℂ) (w : Window 3)
    (H0 : Row0ConvolutionAtRev s z w)
    (hw0 : w 0 = 0)
    (hw1 : w 1 = 0) :
    Row012ConvolutionAtRev s z w := by
  classical
  rcases H0 with ⟨G, hfac, hjet, h3⟩

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0 := by
    -- IMPORTANT: rewrite by the closed form *before* simp can unfold convCoeff to a sum.
    rw [convCoeff_row0Rev_eq_n4 (s := s) (w := w)]
    simp [hw0, hw1]

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0 := by
    rw [convCoeff_row0Rev_eq_n5 (s := s) (w := w)]
    simp [hw0]

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

namespace Row012FromRow0AndCoordsExport
export _root_.Hyperlocal.Targets.XiPacket
  (convCoeff_row0Rev_eq_n4
   convCoeff_row0Rev_eq_n5
   row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_coords)
end Row012FromRow0AndCoordsExport

end XiPacket
end Targets
end Hyperlocal
