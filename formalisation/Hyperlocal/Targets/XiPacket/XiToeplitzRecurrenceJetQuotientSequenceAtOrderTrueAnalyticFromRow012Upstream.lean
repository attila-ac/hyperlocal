import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012UpstreamTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/--
Theorem-side bridge:
package the strict Rec2 true-analytic payload directly from the
Row012-upstream true-analytic bundle.

This is a genuine missing bridge in the current tree.

Important:
this does NOT by itself break the global instance cycle, because
`XiRow012UpstreamTrueAnalytic` is still typically reached through the
tail345/sigma corridor. But it does make the graph more honest and gives the
correct theorem-level producer when an upstream Row012 bundle is already present.
-/
instance (priority := 950)
    [XiRow012UpstreamTrueAnalytic] :
    XiJetQuotRec2AtOrderTrueAnalytic where
  rec2_w0At := by
    intro m s
    exact
      (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic
        (m := m) (s := s)).h_w0At
  rec2_wp2At := by
    intro m s
    exact
      (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic
        (m := m) (s := s)).h_wp2At
  rec2_wp3At := by
    intro m s
    exact
      (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic
        (m := m) (s := s)).h_wp3At

end XiPacket
end Targets
end Hyperlocal
