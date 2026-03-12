/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA.lean

  Legacy ambient compatibility wrapper for the RecurrenceA bridge.

  IMPORTANT:
  * preserve the historical theorem name
  * keep the ambient-instance API surface for downstream compatibility
  * do NOT re-export the theorem-side true-analytic gate from here
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

theorem xiJetQuotRec2AtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  simpa using xiJetQuotRec2AtOrder_fromAnalyticExtractor (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
