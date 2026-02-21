/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA.lean

  Post-Task-A state (DAG-safe):
  the former cycle-safe RecurrenceA axiom boundary is replaced by a theorem
  re-exporting the downstream analytic→recurrence endpoint.

  IMPORTANT:
    This replacement is DAG-safe only once the analytic row012 landing proof
    is independent of Row0SemanticsAtOrder / any RecurrenceA consumers.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Former Route–A boundary, now theorem-level: re-export the analytic extractor endpoint. -/
theorem xiJetQuotRec2AtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  simpa using xiJetQuotRec2AtOrder_fromAnalyticExtractor (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
