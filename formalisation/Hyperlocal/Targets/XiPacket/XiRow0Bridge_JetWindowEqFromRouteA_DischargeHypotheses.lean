/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_DischargeHypotheses.lean

  Produces the three `Hw` hypotheses needed by:
    XiRow0Bridge_JetWindowEqFromRouteA_DischargeLemmas.lean

  Chain:
    (true-analytic) JetQuotRec2 s (padSeq3 (w?At m s))
      + (bridge)     [TAC.JetQuotShiftBridge3AtOrderQuot ...]
      ⇒              IsJet3AtOrderQuot m s z (w?At m s)

  This file is intentionally *parametric* in the bridge instances:
  it compiles even before you install those instances globally.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiJetWindowIsJetAtOrderQuotProviderFromShiftBridge

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

/-
  === The three hypotheses Hw you need downstream ===

  Each theorem is:
    [XiAtOrderSigmaProvider]  -- to get the true-analytic Rec2 fact
    [TAC.JetQuotShiftBridge3AtOrderQuot ...]  -- to turn Rec2 into IsJet3AtOrderQuot
-/

/-- Hw₀: `w0At` is a Route–A quotient 3-jet at anchor `ρ`. -/
theorem Hw_w0At
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s (s.ρ) (w0At m s)] :
    IsJet3AtOrderQuot m s (s.ρ) (w0At m s) := by
  have hrec : JetQuotRec2 s (padSeq3 (w0At m s)) :=
    rec2_w0At_trueAnalytic (m := m) (s := s)
  -- Use the shift-bridge provider (which is definitionally “apply the bridge lemma”).
  exact
    (TAC.instXiJetWindowIsJetAtOrderQuotProviderFromShiftBridge).w0At_isJet3AtOrderQuot
      (m := m) (s := s) hrec

/-- Hw₂: `wp2At` is a Route–A quotient 3-jet at anchor `conj ρ`. -/
theorem Hw_wp2At
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s)] :
    IsJet3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  have hrec : JetQuotRec2 s (padSeq3 (wp2At m s)) :=
    rec2_wp2At_trueAnalytic (m := m) (s := s)
  exact
    (TAC.instXiJetWindowIsJetAtOrderQuotProviderFromShiftBridge).wp2At_isJet3AtOrderQuot
      (m := m) (s := s) hrec

/-- Hw₃: `wp3At` is a Route–A quotient 3-jet at anchor `1 - conj ρ`. -/
theorem Hw_wp3At
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)] :
    IsJet3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  have hrec : JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    rec2_wp3At_trueAnalytic (m := m) (s := s)
  exact
    (TAC.instXiJetWindowIsJetAtOrderQuotProviderFromShiftBridge).wp3At_isJet3AtOrderQuot
      (m := m) (s := s) hrec

end XiPacket
end Targets
end Hyperlocal
