/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderInstallerFromRec2AtOrderTrueAnalytic.lean

  Cycle-safe installer:

    XiAtOrderCoords01Provider := coords01 derived from the TRUE-ANALYTIC Rec2-at-order route.

  This file should be imported only by end-claim cones.
  Upstream/firewall modules must depend only on the interface
    `XiRow0Bridge_AtOrderCoords01Provider`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromRec2AtOrderTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Installer: provides `XiAtOrderCoords01Provider` via the TRUE-ANALYTIC Rec2-at-order route. -/
instance (priority := 50) : XiAtOrderCoords01Provider where
  coords01 := by
    intro m s
    classical
    exact xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
