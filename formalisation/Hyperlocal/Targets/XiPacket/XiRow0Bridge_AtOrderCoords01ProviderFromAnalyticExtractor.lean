/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderFromAnalyticExtractor.lean

  Non-cycle-safe glue instance:

    coords01 provider := xiAtOrderCoords01Out_fromAnalytic

  This imports the extractor-derived theorem provider, so it must NOT be imported by
  analytic-only upstream modules.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

instance : XiAtOrderCoords01Provider where
  coords01 := xiAtOrderCoords01Out_fromAnalytic

end XiPacket
end Targets
end Hyperlocal
