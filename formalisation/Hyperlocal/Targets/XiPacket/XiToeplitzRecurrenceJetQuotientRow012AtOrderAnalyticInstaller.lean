/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstaller.lean

  Installed extractor-facing import surface for the analytic Row012 endpoint.

  Policy:
  * downstream extractor files should import THIS file
  * the upstream analytic landing file remains interface-parametric
  * this preserves the old installed behaviour without contaminating the
    upstream analytic landing node itself

  Current installation:
  * sigma provider via the historical theorem surface
  * coords01 provider via the historical installer surface

  Future work:
  * once downstream consumers are retargeted, these installed imports can be
    replaced independently without reopening cycles in the upstream landing
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticAxiom
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderInstaller

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- stable installed import surface only

end XiPacket
end Targets
end Hyperlocal
