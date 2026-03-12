/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromRecurrenceA.lean

  Stable API: provides the manuscript-facing Prop-valued row012 payload at order.

  IMPORTANT:
  This file must be cycle-safe, so it MUST NOT import the analytic pipeline.
  It is theorem-level: we derive the Prop payload from the clean theorem-side recurrence API.

  2026-03-12 correction:
  the upstream theorem
      `xiJetQuotRec2AtOrder_fromRecurrenceA_theorem`
  now exposes the honest true-analytic gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]

  rather than ambient sigma / coords providers.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012FromSequenceBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/--
Prop-valued row012 payload at order, derived from the clean theorem-side recurrence API.
-/
theorem xiJetQuotRow012PropAtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow012PropAtOrder m s := by
  classical
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)
  exact xiJetQuotRow012PropAtOrder_of_rec2 (m := m) (s := s) Hrec

end XiPacket
end Targets
end Hyperlocal
