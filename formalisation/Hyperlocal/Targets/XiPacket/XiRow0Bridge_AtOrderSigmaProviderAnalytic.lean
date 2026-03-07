/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderAnalytic.lean

  Analytic-cone sigma provider surface.

  This file is the analytic-side retarget point for sigma-at-order.
  Unlike the shared historical theorem shim, it is allowed to depend on the
  clean Rec2 true-analytic route.

  Policy:
  * intended for analytic / extractor-facing cones
  * do NOT use as the shared historical theorem surface
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- re-export only; instance is installed by the imported file

end XiPacket
end Targets
end Hyperlocal
