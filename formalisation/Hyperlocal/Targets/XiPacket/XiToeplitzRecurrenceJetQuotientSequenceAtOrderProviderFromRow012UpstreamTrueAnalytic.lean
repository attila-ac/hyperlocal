/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012UpstreamTrueAnalytic.lean

  Push B (true-analytic Rec2AtOrder discharge):

  Provide the *bundled* recurrence payload
      XiJetQuotRec2AtOrder m s
  by deriving it from the true-analytic Row012 Prop upstream endpoint produced by
  the JetConvolution-driven firewall.

  IMPORTANT:
  * No extractor-facing modules are imported.
  * No Row012 analytic-axiom endpoint modules are imported.

  NOTE (2026-02-28):
  This file is intentionally *lemma-only*; it does NOT install a global
  `XiJetQuotRec2AtOrderProvider` instance. The instance is installed in the
  main landing pad
    `XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic.lean`
  via the interface `XiJetQuotRec2AtOrderTrueAnalytic`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider

-- True-analytic Row012 Prop upstream endpoint (JetConvolution-driven firewall).
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstreamFromConvolutionTrueAnalytic

-- Cycle-safe bridge: Row012PropAtOrder ⇒ Rec2AtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012ToSequenceBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/--
Rec2AtOrder bundle derived from the *true-analytic* Row012 Prop upstream endpoint.

This is the core Push-B payload: it produces the three Rec2 facts for
`w0At/wp2At/wp3At` with no `A0Nonzero` boundary hypothesis.
-/
theorem xiJetQuotRec2AtOrder_fromRow012UpstreamTrueAnalytic
    [XiRow012UpstreamTrueAnalytic]
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  classical
  have Hrow012Prop : XiJetQuotRow012PropAtOrder m s :=
    xiJetQuotRow012PropAtOrder_trueAnalytic_upstream (m := m) (s := s)
  exact xiJetQuotRec2AtOrder_of_row012Prop (m := m) (s := s) Hrow012Prop

end XiPacket
end Targets
end Hyperlocal
