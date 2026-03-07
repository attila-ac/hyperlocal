/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Theorem.lean

  Theorem-backed producer surface for Route-A jet-window equalities.

  Policy:
  * import the axiom-free Core theorem API
  * import the theorem-side producer instance
      `XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider`
  * do NOT import the fallback axiom producer surface
      `XiRow0Bridge_JetWindowEqFromRouteA_Axioms`

  This file is intended for downstream consumer retargeting.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Core
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
