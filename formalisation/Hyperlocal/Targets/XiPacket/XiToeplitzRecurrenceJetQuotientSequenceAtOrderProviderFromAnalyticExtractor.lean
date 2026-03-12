/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor.lean

  Non-cycle-safe legacy glue instance:
    rec2AtOrder provider := historical ambient extractor theorem

  IMPORTANT:
  * this file is the legacy provider shim
  * it must stay on the ambient sigma/coords provider corridor
  * do NOT point it at the theorem-side true-analytic gate
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
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
    have htriple :
        JetQuotRec2 s (padSeq3 (w0At m s)) ∧
        JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
        JetQuotRec2 s (padSeq3 (wp3At m s)) :=
      xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)
    rcases htriple with ⟨hw0, hrest⟩
    rcases hrest with ⟨hwp2, hwp3⟩
    exact ⟨hw0, hwp2, hwp3⟩

end XiPacket
end Targets
end Hyperlocal
