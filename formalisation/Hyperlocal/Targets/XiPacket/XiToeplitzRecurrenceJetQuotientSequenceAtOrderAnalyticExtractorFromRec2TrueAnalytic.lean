/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractorFromRec2TrueAnalytic.lean

  Parallel Route X extractor (analytic -> recurrence) routed through the
  theorem-clean true-analytic upstream Row012 bundle.

  2026-03-12 correction:
  the previous retarget attempt still called
      `xiJetQuotRow012AtOrder_analytic_upstream`
  which explicitly requires
      [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider].
  That reintroduced the old coords01 seam immediately.

  The correct theorem-side source here is instead

      `xiJetQuotRow012AtOrder_trueAnalytic_upstream`

  together with the installed bridge

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
          ==> [XiRow012UpstreamTrueAnalytic].

  This file should therefore depend only on the honest true-analytic gate,
  with no ambient sigma/coords assumptions.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstreamFromConvolutionTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalyticFromRec2TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
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

open Complex
open Hyperlocal.Transport

/--
Parallel extractor theorem using the theorem-clean true-analytic upstream spine.
-/
theorem xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor_fromRec2TrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetQuotRec2 s (padSeq3 (w0At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  classical

  have Hrow012 : XiJetQuotRow012AtOrder m s :=
    xiJetQuotRow012AtOrder_trueAnalytic_upstream (m := m) (s := s)

  have Hrec2 : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s) Hrow012

  exact ⟨Hrec2.h_w0At, Hrec2.h_wp2At, Hrec2.h_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
