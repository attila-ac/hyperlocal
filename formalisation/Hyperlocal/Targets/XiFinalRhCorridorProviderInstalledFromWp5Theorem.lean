import Hyperlocal.Targets.XiFinalRhCorridorProvider
import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderInstalled
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Bundled final RH corridor installed from the single explicit wp5 resonant-branch
theorem gate.

This is a strictly smaller and cleaner seam than the split pair-{2,5} scalar
surface: once `hwp5_res` is available, the bundled final corridor follows.
-/
instance instXiFinalRhCorridorProviderInstalledFromWp5Theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    XiFinalRhCorridorProvider := by
  letI : XiWp5Row0ZeroOnResonantBranchProvider :=
    instXiWp5Row0ZeroOnResonantBranchProviderInstalled
      (hwp5_res := hwp5_res)
  infer_instance

end Targets
end Hyperlocal
