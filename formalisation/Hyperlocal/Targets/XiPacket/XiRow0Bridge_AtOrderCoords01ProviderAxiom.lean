/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderAxiom.lean

  Historical compatibility surface for the coords01 provider.

  2026-03-13 removal step:
  * remove the fallback axiom declaration
  * keep the historical import path stable
  * re-export the theorem-backed installer surface instead
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderInstaller

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- compatibility import surface only

end XiPacket
end Targets
end Hyperlocal
