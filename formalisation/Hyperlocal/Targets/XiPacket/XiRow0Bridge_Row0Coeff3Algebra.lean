/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3Algebra.lean

  Pure algebra: expand
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3
  into the explicit stencil
    (-2) w₂ + σ₂ w₁ − σ₃ w₀.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation

theorem convCoeff3_eq_lincomb
    (s : OffSeed Xi) (w : Transport.Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3
      = (-2 : ℂ) * (w ⟨2, by decide⟩)
        + (JetQuotOp.σ2 s) * (w ⟨1, by decide⟩)
        - (JetQuotOp.σ3 s) * (w ⟨0, by decide⟩) := by
  classical
  -- expand the finite sum over range 4, simp away the zeros, then normalize
  simp [Hyperlocal.Cancellation.convCoeff, row0CoeffSeqRev, winSeqRev,
        Finset.range_succ, Finset.sum_range_succ]
  ring_nf

end XiPacket
end Targets
end Hyperlocal
