import Hyperlocal.Targets.XiFinalRhCorridorProvider
import Hyperlocal.Targets.XiSin2ZeroOnResonantBranchProviderInstalled
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
open scoped Real

/--
Bundled final RH corridor installed from the single prime-2 resonant sine
theorem gate.

Once `h2_res` is available, the standard bridge instances provide the wp5
resonant-branch provider, and hence the bundled final corridor.
-/
instance instXiFinalRhCorridorProviderInstalledFromSin2Theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    XiFinalRhCorridorProvider := by
  letI : XiSin2ZeroOnResonantBranchProvider :=
    instXiSin2ZeroOnResonantBranchProviderInstalled
      (h2_res := h2_res)
  infer_instance

end Targets
end Hyperlocal
