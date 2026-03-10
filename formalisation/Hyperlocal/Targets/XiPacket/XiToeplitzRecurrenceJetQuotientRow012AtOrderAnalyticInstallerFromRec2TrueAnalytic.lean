/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstallerFromRec2TrueAnalytic.lean

  Parallel installed extractor-facing import surface for the analytic Row012 endpoint.

  Policy:
  * leaves the historical installer untouched
  * keeps the strict Rec2-backed TRUE-ANALYTIC corridor in the cone
  * installs theorem-only provider surfaces for:
      - XiAtOrderSigmaProvider
      - XiAtOrderCoords01Provider
  * intended first consumer:
      XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractorFromRec2TrueAnalytic
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticAxiom

-- strict theorem-only sigma route
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticRoot
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticFromUpstream

-- theorem-only coords01 route from sigma + Row012 true-analytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderInstallerFromSigmaAndRow012TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- parallel installed import surface only

end XiPacket
end Targets
end Hyperlocal
