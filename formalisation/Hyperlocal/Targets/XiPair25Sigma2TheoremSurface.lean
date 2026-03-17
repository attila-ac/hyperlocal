import Hyperlocal.Targets.XiSigma2EqTwoDeltaOnResonantBranchAttempt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Honest theorem surface for the pair-{2,5} resonant sigma2 identity.

This is *not* a closed global theorem. It exposes the exact remaining seam:
the standard theorem-side trio together with the wp5 resonant-branch theorem.
-/
theorem sigma2_eq_two_delta_on_resonant_branch_of_wp5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) :=
  sigma2_eq_two_delta_on_resonant_branch_all
    (hwp5_res := hwp5_res)

end Targets
end Hyperlocal
