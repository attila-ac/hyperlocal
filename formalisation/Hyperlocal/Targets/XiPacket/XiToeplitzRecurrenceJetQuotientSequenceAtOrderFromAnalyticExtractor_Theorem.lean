/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor_Theorem.lean

  Parallel theorem-parametric Route-X endpoint (analytic -> recurrence) at order.

  IMPORTANT:
  * this file is theorem-only
  * it does NOT rely on ambient installed producer surfaces
  * all required provider assumptions are explicit in the theorem type
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractorFromRec2TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Parallel theorem-parametric packaged endpoint at order `m`.

Unlike the historical packaged endpoint, this theorem exposes its provider
requirements explicitly.
-/
theorem xiJetQuotRec2AtOrder_fromAnalyticExtractor_theorem
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    XiJetQuotRec2AtOrder m s := by
  classical
  have htriple :
      JetQuotRec2 s (padSeq3 (w0At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor_fromRec2TrueAnalytic
      (m := m) (s := s)
  rcases htriple with ⟨hw0, hrest⟩
  rcases hrest with ⟨hwp2, hwp3⟩
  exact ⟨hw0, hwp2, hwp3⟩

end XiPacket
end Targets
end Hyperlocal
