/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic.lean

  Push B (TRUE-ANALYTIC, boundary-free Rec2AtOrder discharge).

  Goal:
    prove directly (no extractor modules, no boundary hypotheses)

      JetQuotRec2 s (padSeq3 (w0At  m s))
      JetQuotRec2 s (padSeq3 (wp2At m s))
      JetQuotRec2 s (padSeq3 (wp3At m s))

  and install them as the interface:

      [XiJetQuotRec2AtOrderTrueAnalytic]

  Pipeline used (all theorem-level, cycle-safe):

    [XiRow012UpstreamTrueAnalytic]
        ⇒ XiJetQuotRow012PropAtOrder            (JetConvolution-driven firewall)
        ⇒ XiJetQuotRec2AtOrder                  (row012Prop ⇒ Rec2 bridge)
        ⇒ XiJetQuotRec2AtOrderTrueAnalytic      (this file)
        ⇒ XiJetQuotRec2AtOrderProvider          (via interface glue)

  This replaces the older path that went through Row012 reverse-stencil closed-forms
  and therefore needed the auxiliary boundary `[A0Nonzero (s := s)]`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

-- JetConvolution-driven upstream Row012 payload ⇒ Rec2 bundle (no A0Nonzero).
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012UpstreamTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## Push B: the three direct Rec2 lemmas (boundary-free)

These are the exact three statements requested in the progress report.
They are obtained by projecting the bundled payload
`xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic`.
-/

theorem rec2_w0At_trueAnalytic
    [XiRow012UpstreamTrueAnalytic]
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  classical
  simpa using
    (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic (m := m) (s := s)).h_w0At

theorem rec2_wp2At_trueAnalytic
    [XiRow012UpstreamTrueAnalytic]
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  classical
  simpa using
    (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic (m := m) (s := s)).h_wp2At

theorem rec2_wp3At_trueAnalytic
    [XiRow012UpstreamTrueAnalytic]
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  classical
  simpa using
    (xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic (m := m) (s := s)).h_wp3At

/-- Install the Push-B interface (and let the interface-glue provide the provider instance). -/
instance (priority := 1000) [XiRow012UpstreamTrueAnalytic] : XiJetQuotRec2AtOrderTrueAnalytic where
  rec2_w0At  := rec2_w0At_trueAnalytic
  rec2_wp2At := rec2_wp2At_trueAnalytic
  rec2_wp3At := rec2_wp3At_trueAnalytic

end XiPacket
end Targets
end Hyperlocal
