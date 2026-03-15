import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/--
Generic-prime strengthening of the current true-analytic recurrence payload.
-/
class XiJetQuotRec2AtOrderTrueAnalyticPrime : Prop :=
  (rec2_wpAt : ∀ (m : ℕ) (s : OffSeed Xi) (p : ℕ),
      JetQuotRec2 s (padSeq3 (wpAt m s p)))

/--
Any generic-prime payload recovers the old `{2,3}` payload.
-/
instance (priority := 900)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    XiJetQuotRec2AtOrderTrueAnalytic := by
  refine
    { rec2_w0At := XiJetQuotRec2AtOrderTrueAnalytic.rec2_w0At
      rec2_wp2At := ?_
      rec2_wp3At := ?_ }
  · intro m s
    simpa [wp2At] using XiJetQuotRec2AtOrderTrueAnalyticPrime.rec2_wpAt (m := m) (s := s) (p := 2)
  · intro m s
    simpa [wp3At] using XiJetQuotRec2AtOrderTrueAnalyticPrime.rec2_wpAt (m := m) (s := s) (p := 3)

end XiPacket
end Targets
end Hyperlocal
