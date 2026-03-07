/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_RouteAJetCoordProviderFromRec2.lean

  Thin theorem-side producer surface for `RouteAJetCoordProvider`.

  IMPORTANT:
  * Do NOT try to derive `RouteAJetCoordProviderAt` from
    `XiJetQuotRow0WitnessCAtOrder`: that witness does not contain the
    coordinate fields needed here.
  * The actual theorem-backed producer already lives in
      `XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider.lean`
  * This file is therefore just a stable wrapper / import surface.
-/

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
