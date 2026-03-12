/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractorFromRec2TrueAnalyticStrip.lean

  Strip-parallel extractor theorem using the theorem-only Rec2 true-analytic installer.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstallerFromRec2TrueAnalyticStrip
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

theorem xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor_fromRec2TrueAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (w0At m (s : OffSeed Xi))) ∧
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (wp2At m (s : OffSeed Xi))) ∧
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (wp3At m (s : OffSeed Xi))) := by
  classical
  let s0 : OffSeed Xi := (s : OffSeed Xi)

  have Hrow012 : XiJetQuotRow012AtOrder m s0 :=
    xiJetQuotRow012AtOrder_analytic (m := m) (s := s0)

  have Hrec2 : XiJetQuotRec2AtOrder m s0 :=
    xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s0) Hrow012

  exact ⟨Hrec2.h_w0At, Hrec2.h_wp2At, Hrec2.h_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
