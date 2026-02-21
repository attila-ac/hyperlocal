/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Reduce.lean

  PURE ALGEBRA (cycle-safe):

  * proves closed forms for reverse convCoeff at n=4 and n=5
  * proves: Row0ConvolutionAtRev + Row012ExtraLin -> Row012ConvolutionAtRev

  IMPORTANT:
    This file MUST NOT import any "...FromAnalytic" / recurrence extractor modules,
    otherwise it participates in the big Lake cycle.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeAtOrderRow012
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinDefs

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Closed form for the n=4 reverse Cauchy coefficient (algebra-only). -/
theorem convCoeff_rev_eq_n4
    (s : OffSeed Xi) (w : Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4
      = (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) := by
  classical
  simp [convCoeff, row0CoeffSeqRev, winSeqRev, Finset.range_succ]
  ring_nf

/-- Closed form for the n=5 reverse Cauchy coefficient (algebra-only). -/
theorem convCoeff_rev_eq_n5
    (s : OffSeed Xi) (w : Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5
      = (-2 : ℂ) * (w 0) := by
  classical
  simp [convCoeff, row0CoeffSeqRev, winSeqRev, Finset.range_succ]

/--
Upgrade lemma (algebra-only):
Row0ConvolutionAtRev + Row012ExtraLin ⇒ Row012ConvolutionAtRev.
-/
theorem row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_extraLin
    (s : OffSeed Xi) (z : ℂ) (w : Window 3)
    (H0 : Row0ConvolutionAtRev s z w)
    (HL : Row012ExtraLin s w) :
    Row012ConvolutionAtRev s z w := by
  classical
  rcases H0 with ⟨G, hfac, hjet, h3⟩

  have h4coeff : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := w)]
    simpa using HL.h4

  have h5coeff : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := w)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4coeff, h5coeff⟩

end XiPacket
end Targets
end Hyperlocal
