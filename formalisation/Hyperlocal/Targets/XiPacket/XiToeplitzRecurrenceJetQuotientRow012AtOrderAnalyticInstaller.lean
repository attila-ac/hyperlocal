/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstaller.lean

  Historical installed extractor-facing import surface for the analytic Row012 endpoint.

  CHANGE:
  * preserve the historical file / import surface name
  * retarget the implementation to the already-existing Rec2-true-analytic installer
  * this evacuates the old coords01 axiom installer from the analytic extractor spine

  Policy:
  * downstream users keep importing THIS file
  * the underlying installation now comes from the theorem-backed Rec2 corridor
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstallerFromRec2TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- stable installed import surface only

end XiPacket
end Targets
end Hyperlocal
