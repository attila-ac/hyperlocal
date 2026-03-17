import Hyperlocal.Targets.XiSin2ZeroOnResonantBranchTheoremGated
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

/--
The standard sin2 provider installed from the honest pair-{2,5} corridor.
-/
instance instXiSin2ZeroOnResonantBranchProviderTheoremGated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    XiSin2ZeroOnResonantBranchProvider where
  sin2_zero_on_resonant_branch :=
    sin2_zero_on_resonant_branch_pair25_corridor

end Targets
end Hyperlocal
