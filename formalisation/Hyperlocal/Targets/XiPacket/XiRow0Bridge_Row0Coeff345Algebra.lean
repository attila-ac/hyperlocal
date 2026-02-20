/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff345Algebra.lean

  Pure algebra for the reverse-padding Row--0 kernel `row0CoeffSeqRev`
  against the reverse window sequence `winSeqRev`.

  Existing infrastructure already identifies:
    convCoeff ... 3  as the Row--0 dot product.

  This file adds the next two coefficients:
    convCoeff ... 4
    convCoeff ... 5
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Complex
open Hyperlocal.Cancellation

/-- Closed form for the n = 4 reverse Cauchy coefficient. -/
theorem convCoeff4_eq_lincomb
    (s : OffSeed Xi) (w : Transport.Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4
      = (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) := by
  classical
  simp [convCoeff, row0CoeffSeqRev, winSeqRev,
        Finset.range_succ, Finset.sum_range_succ]
  -- normalize additive ordering if simp leaves a commutativity goal
  try ring_nf
  -- fallback in case `ring_nf` has nothing to do (Lean 4.23 rc2 can be picky)
  try simpa [add_comm, add_left_comm, add_assoc]

/-- Closed form for the n = 5 reverse Cauchy coefficient. -/
theorem convCoeff5_eq_lincomb
    (s : OffSeed Xi) (w : Transport.Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5
      = (-2 : ℂ) * (w 0) := by
  classical
  simp [convCoeff, row0CoeffSeqRev, winSeqRev,
        Finset.range_succ, Finset.sum_range_succ]
  try ring_nf
  try simpa [add_comm, add_left_comm, add_assoc]

/-- Same as `convCoeff4_eq_lincomb`, but with `convCoeff` unfolded. -/
theorem convCoeff4_unfold_eq_lincomb
    (s : OffSeed Xi) (w : Transport.Window 3) :
    (∑ i ∈ Finset.range 5,
        row0CoeffSeqRev s i * winSeqRev w (4 - i))
      = (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) := by
  classical
  -- `convCoeff` at n=4 is this sum by definition
  simpa [convCoeff] using (convCoeff4_eq_lincomb (s := s) (w := w))

/-- Same as `convCoeff5_eq_lincomb`, but with `convCoeff` unfolded. -/
theorem convCoeff5_unfold_eq_lincomb
    (s : OffSeed Xi) (w : Transport.Window 3) :
    (∑ i ∈ Finset.range 6,
        row0CoeffSeqRev s i * winSeqRev w (5 - i))
      = (-2 : ℂ) * (w 0) := by
  classical
  simpa [convCoeff] using (convCoeff5_eq_lincomb (s := s) (w := w))

namespace Row0Coeff345AlgebraExport
export _root_.Hyperlocal.Targets.XiPacket
  (convCoeff4_eq_lincomb convCoeff5_eq_lincomb
   convCoeff4_unfold_eq_lincomb convCoeff5_unfold_eq_lincomb)
end Row0Coeff345AlgebraExport

end XiPacket
end Targets
end Hyperlocal
