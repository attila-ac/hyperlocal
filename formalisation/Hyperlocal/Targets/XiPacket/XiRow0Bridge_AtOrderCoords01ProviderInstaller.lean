/-
  Installs the coords01-at-order provider instance.

  Purpose:
  * Upstream analytic-only modules should import installers, not raw axiom provider nodes.
  * This centralizes the import surface needed for `XiAtOrderCoords01Provider` synthesis.

  Note:
  * Today this still routes through the historical provider (possibly axiom-staged).
  * Later we can switch this installer to a theorem-backed provider without touching upstream files.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

-- Current producer node for the coords01 provider.
-- This is the historical placeholder that defines the instance.
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- No new instances here: the instance is provided by the imported producer.
-- This file exists purely as a stable import surface.

end XiPacket
end Targets
end Hyperlocal
