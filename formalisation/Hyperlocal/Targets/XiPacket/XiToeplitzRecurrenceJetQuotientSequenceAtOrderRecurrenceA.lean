/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA.lean

  RecurrenceA bridge surfaces.

  2026-03-13 honest post-axiom state:
  * the old ambient packaged extractor route is no longer admissible as an
    assumption-free surface
  * therefore the exported RecurrenceA wrapper must expose the honest
    theorem-side gate
  * keep the historical theorem names stable, but make their required premises
    explicit

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor_Theorem
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge
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

/-- Historical RecurrenceA theorem name, now on the honest theorem-side gate. -/
theorem xiJetQuotRec2AtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRec2AtOrder m s := by
  simpa using xiJetQuotRec2AtOrder_fromAnalyticExtractor_theorem (m := m) (s := s)

/-- Theorem-gated RecurrenceA theorem on the honest Rec2 true-analytic corridor. -/
theorem xiJetQuotRec2AtOrder_fromRecurrenceA_fromRec2TrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRec2AtOrder m s := by
  let Hrec :
      JetQuotRec2 s (padSeq3 (w0At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor_fromRec2TrueAnalytic
      (m := m) (s := s)
  rcases Hrec with ⟨hw0, hrest⟩
  rcases hrest with ⟨hwp2, hwp3⟩
  exact ⟨hw0, hwp2, hwp3⟩

end XiPacket
end Targets
end Hyperlocal
