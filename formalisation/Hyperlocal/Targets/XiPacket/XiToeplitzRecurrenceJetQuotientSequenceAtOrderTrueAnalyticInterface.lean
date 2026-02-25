/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface.lean

  Serious analytic discharge interface (A):

    class XiJetQuotRec2AtOrderTrueAnalytic : Prop :=
      rec2_w0At  : ∀ m s, JetQuotRec2 s (padSeq3 (w0At m s))
      rec2_wp2At : ∀ m s, JetQuotRec2 s (padSeq3 (wp2At m s))
      rec2_wp3At : ∀ m s, JetQuotRec2 s (padSeq3 (wp3At m s))

  Glue:
    [XiJetQuotRec2AtOrderTrueAnalytic] ⇒ [XiJetQuotRec2AtOrderProvider]

  No axioms introduced here; this is an interface + packaging layer.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- True-analytic recurrence payload for the three AtOrder windows (extractor-free interface). -/
class XiJetQuotRec2AtOrderTrueAnalytic : Prop :=
  (rec2_w0At  : ∀ (m : ℕ) (s : OffSeed Xi), JetQuotRec2 s (padSeq3 (w0At m s)))
  (rec2_wp2At : ∀ (m : ℕ) (s : OffSeed Xi), JetQuotRec2 s (padSeq3 (wp2At m s)))
  (rec2_wp3At : ∀ (m : ℕ) (s : OffSeed Xi), JetQuotRec2 s (padSeq3 (wp3At m s)))

/--
Glue: any true-analytic Rec2 payload installs the standard provider
returning the bundled Prop `XiJetQuotRec2AtOrder m s`.
-/
instance (priority := 1000)
    [XiJetQuotRec2AtOrderTrueAnalytic] : XiJetQuotRec2AtOrderProvider := by
  classical
  refine ⟨?rec2⟩
  intro m s
  refine ⟨?_, ?_, ?_⟩
  · exact XiJetQuotRec2AtOrderTrueAnalytic.rec2_w0At (m := m) (s := s)
  · exact XiJetQuotRec2AtOrderTrueAnalytic.rec2_wp2At (m := m) (s := s)
  · exact XiJetQuotRec2AtOrderTrueAnalytic.rec2_wp3At (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
