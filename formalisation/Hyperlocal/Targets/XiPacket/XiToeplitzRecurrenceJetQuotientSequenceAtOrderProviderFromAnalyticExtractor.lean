/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor.lean

  Non-cycle-safe glue instance:
    rec2AtOrder provider := xiJetQuotRec2AtOrder_fromAnalyticExtractor_theorem

  IMPORTANT:
  * This imports extractor-facing code and must NOT be imported by analytic-only modules.
  * This is a theorem-parametric provider shim.
  * The installed provider is conditional on the explicit theorem-side
    producer surfaces:
      [XiAtOrderSigmaProvider]
      [XiAtOrderCoords01Provider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

instance
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    exact xiJetQuotRec2AtOrder_fromAnalyticExtractor_theorem (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
