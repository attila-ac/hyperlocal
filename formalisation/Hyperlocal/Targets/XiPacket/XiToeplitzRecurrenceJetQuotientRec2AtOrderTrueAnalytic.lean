/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRec2AtOrderTrueAnalytic.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticRecurrencesStrict

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Main Task-A instance (installed at high priority for global resolution). -/
instance (priority := 1000) [XiJetQuotRec2AtOrderProvider] :
    XiJetQuotRec2AtOrderTrueAnalytic where
  rec2_w0At := by
    intro m s
    exact xiJetQuotRec2_padSeq3_w0At_fromAnalytic_strict (m := m) (s := s)
  rec2_wp2At := by
    intro m s
    exact xiJetQuotRec2_padSeq3_wp2At_fromAnalytic_strict (m := m) (s := s)
  rec2_wp3At := by
    intro m s
    exact xiJetQuotRec2_padSeq3_wp3At_fromAnalytic_strict (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
