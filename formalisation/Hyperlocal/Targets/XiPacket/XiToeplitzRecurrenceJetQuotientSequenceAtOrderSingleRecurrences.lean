/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderSingleRecurrences.lean

  Convenience export layer (cycle-safe, theorem-level):

  Expose the three *single-statement* padded-sequence recurrences

      JetQuotRec2 s (padSeq3 (w0At m s))
      JetQuotRec2 s (padSeq3 (wp2At m s))
      JetQuotRec2 s (padSeq3 (wp3At m s))

  under stable names.

  NOTE:
  These are theorem-level consequences of the existing Route–A landing pad
  `xiJetQuotRec2AtOrder_fromRecurrenceA`.

  When the manuscript-facing axiom is eventually replaced by the true analytic
  extractor proof, these theorems become fully analytic with no API change.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012FromSequenceBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Single-statement recurrence for the padded jet window `w0At`. -/
theorem xiJetQuotRec2_padSeq3_w0At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRecurrenceA (m := m) (s := s)).h_w0At

/-- Single-statement recurrence for the padded prime window `wp2At`. -/
theorem xiJetQuotRec2_padSeq3_wp2At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRecurrenceA (m := m) (s := s)).h_wp2At

/-- Single-statement recurrence for the padded prime window `wp3At`. -/
theorem xiJetQuotRec2_padSeq3_wp3At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRecurrenceA (m := m) (s := s)).h_wp3At

/--
One-line derivation of the manuscript-facing row012 Prop payload from the bundled recurrence.

This is the promised “row012 drops out by one lemma call” endpoint.
-/
theorem xiJetQuotRow012PropAtOrder_fromRecurrencePayload_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow012PropAtOrder m s := by
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRecurrenceA (m := m) (s := s)
  exact xiJetQuotRow012PropAtOrder_of_rec2 (m := m) (s := s) Hrec

end XiPacket
end Targets
end Hyperlocal
