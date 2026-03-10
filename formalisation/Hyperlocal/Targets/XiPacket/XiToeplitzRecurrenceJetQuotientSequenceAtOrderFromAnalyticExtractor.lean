/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor.lean

  Route-X endpoint (analytic -> recurrence) at order.

  Updated:
  this packaged endpoint now consumes the parallel theorem-only extractor spine
  rather than the historical installed extractor surface.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractorFromRec2TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Route-X (analytic -> recurrence) packaged endpoint at order `m`. -/
theorem xiJetQuotRec2AtOrder_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  classical
  rcases
      xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor_fromRec2TrueAnalytic
        (m := m) (s := s)
    with ⟨hw0, hwp2, hwp3⟩
  exact ⟨hw0, hwp2, hwp3⟩

end XiPacket
end Targets
end Hyperlocal
