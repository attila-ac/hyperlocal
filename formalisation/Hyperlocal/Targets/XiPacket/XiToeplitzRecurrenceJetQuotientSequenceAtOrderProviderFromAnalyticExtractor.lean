/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor.lean

  Non-cycle-safe glue instance:
    rec2AtOrder provider := xiJetQuotRec2AtOrder_fromAnalyticExtractor

  IMPORTANT:
  * This imports extractor-facing code and must NOT be imported by analytic-only modules.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

instance : XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := xiJetQuotRec2AtOrder_fromAnalyticExtractor

end XiPacket
end Targets
end Hyperlocal
