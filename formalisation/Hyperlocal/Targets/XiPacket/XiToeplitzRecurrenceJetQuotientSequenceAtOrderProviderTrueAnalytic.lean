/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic.lean

  Front R2: TRUE-ANALYTIC Rec2AtOrder discharge.

  New (2026-02-28):
  Make Rec2 depend only on the JetConvolution-driven Row012 convolution gate:

      [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
        ⇒ Rec2 payload
        ⇒ [XiJetQuotRec2AtOrderTrueAnalytic]

  (Upstream/installer layers are handled by the root import file.)
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

-- This bundles Rec2 from the Row012Upstream payload; we’ll let typeclass search build Upstream if needed.
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012UpstreamTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## Front R2.1: the three direct Rec2 lemmas (now Row012Convolution-driven)

We assume only `[XiRow012ConvolutionAtRevAtOrderTrueAnalytic]`.
Then we let typeclass search install `[XiRow012UpstreamTrueAnalytic]` (via its
priority-1000 instance) and project the bundled Rec2 payload.
-/

theorem rec2_w0At_trueAnalytic
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  classical
  haveI : XiRow012UpstreamTrueAnalytic := inferInstance
  simpa using
    (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic (m := m) (s := s)).h_w0At

theorem rec2_wp2At_trueAnalytic
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  classical
  haveI : XiRow012UpstreamTrueAnalytic := inferInstance
  simpa using
    (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic (m := m) (s := s)).h_wp2At

theorem rec2_wp3At_trueAnalytic
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  classical
  haveI : XiRow012UpstreamTrueAnalytic := inferInstance
  simpa using
    (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic (m := m) (s := s)).h_wp3At

/--
Front R2.3: strict true-analytic Rec2 instance.

Priority 1000 so it wins over any legacy/axiom shims.
-/
instance (priority := 1000)
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic] :
    XiJetQuotRec2AtOrderTrueAnalytic where
  rec2_w0At  := rec2_w0At_trueAnalytic
  rec2_wp2At := rec2_wp2At_trueAnalytic
  rec2_wp3At := rec2_wp3At_trueAnalytic

end XiPacket
end Targets
end Hyperlocal
