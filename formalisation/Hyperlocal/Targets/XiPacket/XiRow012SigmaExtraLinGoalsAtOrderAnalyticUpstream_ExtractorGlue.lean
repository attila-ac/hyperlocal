/-
  Hyperlocal/Targets/XiPacket/XiRow012SigmaExtraLinGoalsAtOrderAnalyticUpstream_ExtractorGlue.lean

  Non-cycle-safe glue:
  * installs coords01 provider instance from analytic extractor
  * re-exports the packaging theorem
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow012SigmaExtraLinGoalsAtOrderAnalyticUpstream

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace Row012AnalyticUpstreamGlueExport
export _root_.Hyperlocal.Targets.XiPacket (xiRow012SigmaExtraLinGoalsAtOrder_analytic_upstream)
end Row012AnalyticUpstreamGlueExport

end XiPacket
end Targets
end Hyperlocal
