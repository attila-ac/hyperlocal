/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderInstallerFromRec2AtOrderTrueAnalytic.lean

  Conditional installer for coords01-at-order from the TRUE-ANALYTIC Rec2 route.

  2026-03-12 retarget:
  the provider now follows the theorem-routed sigma+Row012 true-analytic corridor,
  so it must expose the corresponding explicit premises.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromRec2AtOrderTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

instance (priority := 50)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiAtOrderCoords01Provider where
  coords01 := by
    intro m s
    classical
    exact xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
