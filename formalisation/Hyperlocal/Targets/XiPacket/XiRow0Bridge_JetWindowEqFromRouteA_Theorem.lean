/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Theorem.lean

  Theorem-backed producer surface for Route-A jet-window equalities.

  Policy:
  * import the axiom-free Core theorem API
  * import the direct theorem-side eq-provider installer
      [RouteAJetCoordProvider] => [TAC.XiJetWindowEqAtOrderQuotProvider]
  * import the theorem-side wc coord installer
      [RouteAWcScalarProvider] => [RouteAWcCoordProvider]
  * import the reverse coord-provider installer
      [TAC.XiJetWindowEqAtOrderQuotProvider] [RouteAWcCoordProvider]
          => [RouteAJetCoordProvider]
  * do NOT import fallback axiom producer surfaces
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Core
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_QuotEqProviderFromCoordProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcCoordProviderFromScalars
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- stable theorem-side import surface only

end XiPacket
end Targets
end Hyperlocal
