/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem.lean

  Clean theorem-parametric RecurrenceA bridge.

  IMPORTANT:
  * this is the theorem-side replacement for the historical ambient RecurrenceA shim
  * it exposes the required producer assumptions explicitly
  * it re-exports the clean Route-X theorem corridor

  2026-03-12 correction:
  the downstream Route-X theorem
      `xiJetQuotRec2AtOrder_fromAnalyticExtractor_theorem`
  now exposes the honest true-analytic gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]

  rather than ambient
      [XiAtOrderSigmaProvider]
      [XiAtOrderCoords01Provider].

  So this RecurrenceA theorem wrapper must align to the same gate.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor_Theorem
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

theorem xiJetQuotRec2AtOrder_fromRecurrenceA_theorem
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRec2AtOrder m s := by
  simpa using xiJetQuotRec2AtOrder_fromAnalyticExtractor_theorem (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
