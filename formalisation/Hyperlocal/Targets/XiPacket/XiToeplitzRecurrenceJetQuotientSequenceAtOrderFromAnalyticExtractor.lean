/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor.lean

  Historical packaged Route-X endpoint (analytic -> recurrence) at order.

  2026-03-13 post-retarget policy:
  * keep this file as a stable import path only
  * do NOT redeclare `xiJetQuotRec2AtOrder_fromAnalyticExtractor` here
  * do NOT import `...SequenceAtOrderRecurrenceA`, since that file already sits
    downstream of this historical path and would create an import cycle
  * downstream users may continue importing this file unchanged
-/

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- compatibility import surface only

end XiPacket
end Targets
end Hyperlocal
