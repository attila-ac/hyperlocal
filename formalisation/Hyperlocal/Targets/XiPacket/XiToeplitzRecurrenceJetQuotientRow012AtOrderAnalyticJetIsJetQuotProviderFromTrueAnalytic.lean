/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotProviderFromTrueAnalytic.lean

  E2 completion:
  Package the three quotient jet facts as a global provider instance

      [TAC.XiJetWindowIsJetAtOrderQuotProvider]

  from:
    * true-analytic Rec2 provider on padSeq3(w?At)
    * ShiftBridge instances (available once an Eq-provider exists)

  This file introduces NO axioms.

  NOTE:
  We work at the canonical Route–E anchors `TAC.z_w0At/z_wp2At/z_wp3At`
  so the downstream Eq-provider / ShiftBridge installer stack stays hands-free.

  Editor/CLI robustness note (2026-03-05):
  The Rec2-at-order true-analytic source for (w0At/wp2At/wp3At) is gated by
  `[XiRow012ConvolutionAtRevAtOrderTrueAnalytic]`.  When VS Code elaborates this file
  in isolation (`lake setup-file`), that instance may not be present unless we import
  its producer chain.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic

-- Producer chain for `[XiRow012ConvolutionAtRevAtOrderTrueAnalytic]`.
-- (existing analytic Row012 endpoint) ⇒ `XiRow012UpstreamTrueAnalytic`
-- ⇒ `XiRow012ConvolutionAtRevAtOrderTrueAnalytic`.
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticFromUpstream

import Hyperlocal.Targets.XiPacket.XiRouteA_QuotShiftBridgeInstancesFromTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/--
E2: the quotient-jet provider is theorem-level once you have:

* true-analytic sigma provider (to get the Rec2 facts), and
* an Eq-provider (to get the ShiftBridge instances via the installer).

No axioms; pure glue.
-/
instance (priority := 1000)
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    TAC.XiJetWindowIsJetAtOrderQuotProvider := by
  classical
  refine ⟨?_, ?_, ?_⟩

  · intro m s
    -- Recurrence from the true-analytic provider
    have hw : JetQuotRec2 s (padSeq3 (w0At m s)) :=
      rec2_w0At_trueAnalytic (m := m) (s := s)
    -- ShiftBridge instance is now available (imported installer + Eq-provider)
    -- and we use the stable bridge lemma:
    simpa using
      (TAC.isJet3AtOrderQuot_w0At_of_rec2 (m := m) (s := s) (z := TAC.z_w0At s) hw)

  · intro m s
    have hw : JetQuotRec2 s (padSeq3 (wp2At m s)) :=
      rec2_wp2At_trueAnalytic (m := m) (s := s)
    simpa using
      (TAC.isJet3AtOrderQuot_wp2At_of_rec2 (m := m) (s := s) (z := TAC.z_wp2At s) hw)

  · intro m s
    have hw : JetQuotRec2 s (padSeq3 (wp3At m s)) :=
      rec2_wp3At_trueAnalytic (m := m) (s := s)
    simpa using
      (TAC.isJet3AtOrderQuot_wp3At_of_rec2 (m := m) (s := s) (z := TAC.z_wp3At s) hw)

end XiPacket
end Targets
end Hyperlocal
