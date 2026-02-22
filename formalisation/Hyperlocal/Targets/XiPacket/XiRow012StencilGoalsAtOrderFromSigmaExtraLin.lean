/-
  Hyperlocal/Targets/XiPacket/XiRow012StencilGoalsAtOrderFromSigmaExtraLin.lean

  Pure algebra bridge:

    XiRow012SigmaExtraLinGoalsAtOrder  ==>  XiRow012StencilGoalsAtOrder.

  This is cycle-safe: it uses only definitional rewrites and the closed-form
  convCoeff rewrites already used in the cycle-safe Route–C discharge.
-/

import Hyperlocal.Targets.XiPacket.XiRow012StencilGoalsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow012SigmaExtraLinGoalsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Reduce

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Convert semantic (sigma+extraLin) goals into raw convCoeff stencil goals. -/
theorem xiRow012StencilGoalsAtOrder_of_sigmaExtraLinGoals
    (m : ℕ) (s : OffSeed Xi)
    (H : _root_.Hyperlocal.Targets.XiPacket.XiRow012SigmaExtraLinGoalsAtOrder m s) :
    XiRow012StencilGoalsAtOrder m s := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · -- w0At, n=3
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using H.hw0_sigma
  · -- w0At, n=4
    rw [convCoeff_rev_eq_n4 (s := s) (w := w0At m s)]
    simpa using H.hw0_ex.h4
  · -- w0At, n=5
    rw [convCoeff_rev_eq_n5 (s := s) (w := w0At m s)]
    simpa using H.hw0_ex.h5

  · -- wp2At, n=3
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using H.hwp2_sigma
  · -- wp2At, n=4
    rw [convCoeff_rev_eq_n4 (s := s) (w := wp2At m s)]
    simpa using H.hwp2_ex.h4
  · -- wp2At, n=5
    rw [convCoeff_rev_eq_n5 (s := s) (w := wp2At m s)]
    simpa using H.hwp2_ex.h5

  · -- wp3At, n=3
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using H.hwp3_sigma
  · -- wp3At, n=4
    rw [convCoeff_rev_eq_n4 (s := s) (w := wp3At m s)]
    simpa using H.hwp3_ex.h4
  · -- wp3At, n=5
    rw [convCoeff_rev_eq_n5 (s := s) (w := wp3At m s)]
    simpa using H.hwp3_ex.h5

end XiPacket
end Targets
end Hyperlocal
