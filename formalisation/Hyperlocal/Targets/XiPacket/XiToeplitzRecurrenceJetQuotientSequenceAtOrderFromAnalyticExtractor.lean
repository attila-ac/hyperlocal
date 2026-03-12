/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor.lean

  Legacy packaged Route-X endpoint (analytic -> recurrence) at order.

  IMPORTANT:
  * this file is the legacy ambient compatibility surface
  * it must remain on the historical sigma/coords provider corridor
  * do NOT re-export the theorem-side true-analytic gate from here

  2026-03-12 compatibility repair:
  * `XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor_Theorem`
    now lives on the honest gate

        [XiJetQuotRec2AtOrderTrueAnalytic]
        [TAC.XiJetWindowEqAtOrderQuotProvider]

    and therefore is not an admissible dependency for this legacy wrapper.
  * instead, rebuild the bundled recurrence payload directly from the historical
    ambient extractor theorem
        `xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Legacy packaged endpoint on the historical ambient sigma/coords corridor. -/
theorem xiJetQuotRec2AtOrder_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  classical
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
