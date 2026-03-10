/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem.lean

  Clean theorem-parametric RecurrenceA bridge.

  IMPORTANT:
  * this is the theorem-side replacement for the historical ambient RecurrenceA shim
  * it exposes the required producer assumptions explicitly
  * it re-exports the clean Route-X theorem corridor
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

theorem xiJetQuotRec2AtOrder_fromRecurrenceA_theorem
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    XiJetQuotRec2AtOrder m s := by
  simpa using xiJetQuotRec2AtOrder_fromAnalyticExtractor_theorem (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
