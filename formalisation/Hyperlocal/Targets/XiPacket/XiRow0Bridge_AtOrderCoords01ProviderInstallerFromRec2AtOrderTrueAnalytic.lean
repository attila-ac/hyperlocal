/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderInstallerFromRec2AtOrderTrueAnalytic.lean

  ROOT-FREE conditional installer:

    [XiJetQuotRec2AtOrderProvider] -> [XiAtOrderCoords01Provider]

  IMPORTANT:
  * this is no longer a zero-premise installer
  * do NOT import this into the analytic installer cone
  * it is for downstream / end-claim cones where a Rec2 provider is already present
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromRec2AtOrderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

instance (priority := 50)
    [XiJetQuotRec2AtOrderProvider] : XiAtOrderCoords01Provider where
  coords01 := by
    intro m s
    classical
    exact xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
