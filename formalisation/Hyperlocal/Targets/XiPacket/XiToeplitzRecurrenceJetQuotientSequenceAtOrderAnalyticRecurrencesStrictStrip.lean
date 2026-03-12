/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticRecurrencesStrictStrip.lean

  STRICT strip-specialised theorem layer for Task A.

  Goal:
    expose the three Rec2 facts for the canonical windows
      `w0At`, `wp2At`, `wp3At`
    as plain theorems on the strip branch.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012UpstreamTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticStripRoot

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Plain strip theorem: recurrence for `w0At`. -/
theorem xiJetQuotRec2_padSeq3_w0At_fromAnalytic_strict_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (w0At m (s : OffSeed Xi))) := by
  exact (xiJetQuotRec2AtOrder_provided (m := m) (s := (s : OffSeed Xi))).h_w0At

/-- Plain strip theorem: recurrence for `wp2At`. -/
theorem xiJetQuotRec2_padSeq3_wp2At_fromAnalytic_strict_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (wp2At m (s : OffSeed Xi))) := by
  exact (xiJetQuotRec2AtOrder_provided (m := m) (s := (s : OffSeed Xi))).h_wp2At

/-- Plain strip theorem: recurrence for `wp3At`. -/
theorem xiJetQuotRec2_padSeq3_wp3At_fromAnalytic_strict_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 (s : OffSeed Xi) (padSeq3 (wp3At m (s : OffSeed Xi))) := by
  exact (xiJetQuotRec2AtOrder_provided (m := m) (s := (s : OffSeed Xi))).h_wp3At

end XiPacket
end Targets
end Hyperlocal
