/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractorFromRec2TrueAnalyticStrip.lean

  Strip-parallel extractor theorem using the theorem-clean true-analytic upstream spine.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstreamFromConvolutionTrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalyticFromRec2TrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport

theorem xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor_fromRec2TrueAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (w0At m (s : OffSeed Xi))) ∧
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (wp2At m (s : OffSeed Xi))) ∧
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (wp3At m (s : OffSeed Xi))) := by
  classical
  let s0 : OffSeed Xi := (s : OffSeed Xi)

  have Hrow012 : XiJetQuotRow012AtOrder m s0 :=
    xiJetQuotRow012AtOrder_trueAnalytic_upstream_strip (m := m) (s := s)

  have Hrec2 : XiJetQuotRec2AtOrder m s0 :=
    xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s0) Hrow012

  exact ⟨Hrec2.h_w0At, Hrec2.h_wp2At, Hrec2.h_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
