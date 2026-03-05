/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderInstallerFromAnalyticExtractor.lean

  End-claim installer: installs theorem-backed coords01 provider via the
  AnalyticExtractor route (NOT the Rec2-TrueAnalytic root chain).

  Policy:
  * Import this ONLY in end-claim cones (OneButton / offSeedPhaseLock / RH).
  * Do NOT import this from analytic-only upstream / extractor-safe modules.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
-- stable import surface only
end XiPacket
end Targets
end Hyperlocal
