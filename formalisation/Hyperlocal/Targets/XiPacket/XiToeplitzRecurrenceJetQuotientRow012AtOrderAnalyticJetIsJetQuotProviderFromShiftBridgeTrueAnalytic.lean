/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotProviderFromShiftBridgeTrueAnalytic.lean

  Non-circular theorem-side root for

      [TAC.XiJetWindowIsJetAtOrderQuotProvider]

  using:
    * true-analytic Rec2 facts on padSeq3(w?At), and
    * shift-bridge instances available from the quotient Eq-provider installer surface.

  IMPORTANT:
  We do NOT import the legacy file
    `XiJetWindowIsJetAtOrderQuotProviderFromShiftBridge.lean`
  because that file redeclares the class name
    `TAC.XiJetWindowIsJetAtOrderQuotProvider`
  and is therefore incompatible with the canonical provider universe used by
    `XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets.lean`.

  Instead, we re-express the same non-circular instance body here against the
  canonical class.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_Row012ConvolutionInstanceFromUpstream
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

instance (priority := 1000)
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    TAC.XiJetWindowIsJetAtOrderQuotProvider := by
  classical
  refine ⟨?_, ?_, ?_⟩

  · intro m s
    have hrec : JetQuotRec2 s (padSeq3 (w0At m s)) :=
      rec2_w0At_trueAnalytic (m := m) (s := s)
    simpa using
      (TAC.isJet3AtOrderQuot_w0At_of_rec2 (m := m) (s := s) (z := TAC.z_w0At s) hrec)

  · intro m s
    have hrec : JetQuotRec2 s (padSeq3 (wp2At m s)) :=
      rec2_wp2At_trueAnalytic (m := m) (s := s)
    simpa using
      (TAC.isJet3AtOrderQuot_wp2At_of_rec2 (m := m) (s := s) (z := TAC.z_wp2At s) hrec)

  · intro m s
    have hrec : JetQuotRec2 s (padSeq3 (wp3At m s)) :=
      rec2_wp3At_trueAnalytic (m := m) (s := s)
    simpa using
      (TAC.isJet3AtOrderQuot_wp3At_of_rec2 (m := m) (s := s) (z := TAC.z_wp3At s) hrec)

end XiPacket
end Targets
end Hyperlocal
