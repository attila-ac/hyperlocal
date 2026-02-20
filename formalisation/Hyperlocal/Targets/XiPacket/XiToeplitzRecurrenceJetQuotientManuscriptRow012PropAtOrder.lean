/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientManuscriptRow012PropAtOrder.lean

  Formerly: this file contained the *last* axiom
    `xiJetQuotRow012PropAtOrder_fromRecurrenceA`.

  Now: we prove it axiom-free by composing:
    Analytic inputs
      → JetQuotRec2 s (padSeq3 (w0At/wp2At/wp3At))
      → XiJetQuotRow012PropAtOrder m s
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012FromSequenceBridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticRecurrences

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Manuscript Row012 landing spot (Prop-valued, axiom-free):

`XiJetQuotRow012PropAtOrder m s` follows from the analytic extractor recurrences
for the three padded sequences, via the reverse bridge
`xiJetQuotRow012PropAtOrder_of_rec2`.
-/
theorem xiJetQuotRow012PropAtOrder_fromAnalyticRecurrences (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow012PropAtOrder m s := by
  -- analytic → three recurrences
  have hw0  : JetQuotRec2 s (padSeq3 (w0At m s)) :=
    xiJetQuotRec2_padSeq3_w0At_fromAnalytic (m := m) (s := s)
  have hwp2 : JetQuotRec2 s (padSeq3 (wp2At m s)) :=
    xiJetQuotRec2_padSeq3_wp2At_fromAnalytic (m := m) (s := s)
  have hwp3 : JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    xiJetQuotRec2_padSeq3_wp3At_fromAnalytic (m := m) (s := s)

  -- recurrences → row012 prop payload
  have Hrec2 : XiJetQuotRec2AtOrder m s := ⟨hw0, hwp2, hwp3⟩
  exact xiJetQuotRow012PropAtOrder_of_rec2 (m := m) (s := s) Hrec2

end XiPacket
end Targets
end Hyperlocal
