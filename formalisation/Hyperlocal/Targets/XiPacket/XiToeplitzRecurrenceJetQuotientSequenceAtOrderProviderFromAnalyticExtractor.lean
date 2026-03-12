/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor.lean

  Provider / theorem bridge for the Route-X extractor.

  IMPORTANT:
  * keep the historical ambient provider instance unchanged
  * add a theorem-gated sibling payload on the honest Rec2 true-analytic corridor
  * do NOT install a second competing provider instance here yet
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/--
Historical ambient provider instance on the sigma/coords corridor.
-/
instance
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    have htriple :
        JetQuotRec2 s (padSeq3 (w0At m s)) ∧
        JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
        JetQuotRec2 s (padSeq3 (wp3At m s)) :=
      xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)
    rcases htriple with ⟨hw0, hrest⟩
    rcases hrest with ⟨hwp2, hwp3⟩
    exact ⟨hw0, hwp2, hwp3⟩

/--
Theorem-gated packaged recurrence payload on the honest Rec2 true-analytic corridor.

This is intentionally a theorem, not an installed instance, so the legacy
ambient provider lane stays stable while downstream theorem consumers gain an
admissible retarget point.
-/
theorem xiJetQuotRec2AtOrder_fromAnalyticExtractor_fromRec2TrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRec2AtOrder m s := by
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
