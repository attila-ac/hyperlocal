import Hyperlocal.Targets.XiFinalRhCorridorProvider
import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderInstalledFromTrueAnalyticPrime
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
Final corridor installer from the theorem-side trio plus the genuine
generic-prime true-analytic producer.
-/
instance instXiFinalRhCorridorProviderInstalledFromTrueAnalyticPrime
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    XiFinalRhCorridorProvider := by
  infer_instance

end Targets
end Hyperlocal
