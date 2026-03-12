/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotProviderFromTrueAnalytic.lean

  E2 completion:
  Package the three quotient jet facts as a global provider instance

      [TAC.XiJetWindowIsJetAtOrderQuotProvider]

  from:
    * true-analytic Rec2 provider on padSeq3(w?At)
    * ShiftBridge instances (available once an Eq-provider exists)

  2026-03-12 fix:
  the Rec2 true-analytic lemmas
      `rec2_w0At_trueAnalytic`, `rec2_wp2At_trueAnalytic`, `rec2_wp3At_trueAnalytic`
  are gated by
      [XiRow012ConvolutionAtRevAtOrderTrueAnalytic].
  Importing its producer chain is not enough here; the required class must be
  present in the instance context explicitly.

  This file introduces NO axioms.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
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

* true-analytic Row012 reverse-convolution,
* true-analytic sigma provider, and
* an Eq-provider (to get the ShiftBridge instances via the installer).

No axioms; pure glue.
-/
instance (priority := 1000)
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    TAC.XiJetWindowIsJetAtOrderQuotProvider := by
  classical
  refine ⟨?_, ?_, ?_⟩

  · intro m s
    have hw : JetQuotRec2 s (padSeq3 (w0At m s)) :=
      rec2_w0At_trueAnalytic (m := m) (s := s)
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
