/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor.lean

  Route X extractor (analytic → recurrence):
  derive the padded-sequence JetQuotRec2 triple from the analytic row012 target.

  No new axioms here. The ONLY axiom is in:
    XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalytic.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Extractor theorem (the endpoint should `simpa` from):
produces the three padded-sequence recurrences at order `m`.
-/
theorem xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (w0At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  -- 1) analytic row012 contract (currently axiom-backed, but exposed as a def)
  have Hrow012 : XiJetQuotRow012AtOrder m s :=
    xiJetQuotRow012AtOrder_fromAnalytic (m := m) (s := s)

  -- 2) row012 → rec2 bundle (already green in your repo)
  have Hrec2 : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s) Hrow012

  -- 3) project the three padded-sequence recurrences
  exact ⟨Hrec2.h_w0At, Hrec2.h_wp2At, Hrec2.h_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
