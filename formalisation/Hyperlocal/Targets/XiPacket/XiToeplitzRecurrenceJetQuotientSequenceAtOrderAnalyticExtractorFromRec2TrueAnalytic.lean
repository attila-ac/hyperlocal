/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractorFromRec2TrueAnalytic.lean

  Parallel Route X extractor (analytic -> recurrence), but with the installed
  provider surface forced onto the theorem-only Rec2 true-analytic corridor.

  This file is intentionally parallel to the historical
  `XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor.lean`
  and is meant for downstream theorem consumers that should avoid the old
  installer seam.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstallerFromRec2TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
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
Parallel extractor theorem using the theorem-only analytic installer spine.
-/
theorem xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor_fromRec2TrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    JetQuotRec2 s (padSeq3 (w0At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  classical
  have Hrow012 : XiJetQuotRow012AtOrder m s :=
    xiJetQuotRow012AtOrder_analytic (m := m) (s := s)

  have Hrec2 : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s) Hrow012

  exact ⟨Hrec2.h_w0At, Hrec2.h_wp2At, Hrec2.h_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
