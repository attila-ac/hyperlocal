import Hyperlocal.Targets.XiSigma2EqTwoDeltaOnResonantBranchAttempt
import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderBridges
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
Installed resonant-branch sigma2 provider from the existing theorem surface.
-/
instance instXiSigma2EqTwoDeltaOnResonantBranchProviderInstalled
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    XiSigma2EqTwoDeltaOnResonantBranchProvider where
  sigma2_eq_two_delta_on_resonant_branch :=
    sigma2_eq_two_delta_on_resonant_branch_all
      (hwp5_res := hwp5_res)

end Targets
end Hyperlocal
