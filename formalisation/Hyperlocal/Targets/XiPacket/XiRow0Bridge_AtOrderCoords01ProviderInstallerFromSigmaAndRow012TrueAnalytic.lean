/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderInstallerFromSigmaAndRow012TrueAnalytic.lean

  End-cone installer for coords01-at-order from the theorem route

    xiAtOrderCoords01Out_fromSigmaAndRow012TrueAnalytic

  IMPORTANT:
  * do not import this file in upstream/firewall modules
  * intended import sites: XiPhaseLock / OneButton / RH end-claim cones
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromSigmaAndRow012TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

instance (priority := 50)
    [XiAtOrderSigmaProvider]
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero] :
    XiAtOrderCoords01Provider where
  coords01 := by
    intro m s
    classical
    exact xiAtOrderCoords01Out_fromSigmaAndRow012TrueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
