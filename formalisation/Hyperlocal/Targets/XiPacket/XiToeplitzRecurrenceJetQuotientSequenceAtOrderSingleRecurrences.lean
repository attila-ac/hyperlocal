/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderSingleRecurrences.lean

  Convenience export layer (cycle-safe, theorem-level):

  Expose the three single-statement padded-sequence recurrences

      JetQuotRec2 s (padSeq3 (w0At m s))
      JetQuotRec2 s (padSeq3 (wp2At m s))
      JetQuotRec2 s (padSeq3 (wp3At m s))

  under stable names.

  NOTE:
  These are theorem-level consequences of the clean theorem-side Route-A landing pad
  `xiJetQuotRec2AtOrder_fromRecurrenceA_theorem`.

  2026-03-12 correction:
  the upstream theorem now exposes the honest true-analytic gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]

  rather than ambient sigma / coords providers.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012FromSequenceBridge

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

/-- Single-statement recurrence for the padded jet window `w0At`. -/
theorem xiJetQuotRec2_padSeq3_w0At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)).h_w0At

/-- Single-statement recurrence for the padded prime window `wp2At`. -/
theorem xiJetQuotRec2_padSeq3_wp2At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)).h_wp2At

/-- Single-statement recurrence for the padded prime window `wp3At`. -/
theorem xiJetQuotRec2_padSeq3_wp3At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)).h_wp3At

/--
One-line derivation of the manuscript-facing row012 Prop payload from the bundled recurrence.
-/
theorem xiJetQuotRow012PropAtOrder_fromRecurrencePayload_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow012PropAtOrder m s := by
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)
  exact xiJetQuotRow012PropAtOrder_of_rec2 (m := m) (s := s) Hrec

end XiPacket
end Targets
end Hyperlocal
