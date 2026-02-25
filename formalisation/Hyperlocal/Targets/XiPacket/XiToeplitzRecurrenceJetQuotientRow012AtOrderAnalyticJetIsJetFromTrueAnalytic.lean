/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetFromTrueAnalytic.lean

  True-analytic source of quotient-jet facts for the three pivot windows.

  IMPORTANT FIX (2026-02-25):
  * Do NOT define `Hyperlocal.Targets.XiPacket.TAC.z_w0At/z_wp2At/z_wp3At` here
    (those are introduced by the JetProvider/ProviderFromJets layers).
  * If you want local anchor names, define them in the *XiPacket* namespace.

  This file is intentionally *parametric* in the bridge instances:
  it proves the jet facts from:
      (true-analytic) JetQuotRec2 on padSeq3(w?At)
    + (bridge)       [TAC.JetQuotShiftBridge3AtOrderQuot ...]
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrderQuot

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Canonical quotient anchor for `w0At`: the Route–A point `ρ`. -/
def z_w0At (s : OffSeed Xi) : ℂ := s.ρ

/-- Canonical quotient anchor for `wp2At`: the Route–A point `conj ρ`. -/
def z_wp2At (s : OffSeed Xi) : ℂ := (starRingEnd ℂ) s.ρ

/-- Canonical quotient anchor for `wp3At`: the Route–A point `1 - conj ρ`. -/
def z_wp3At (s : OffSeed Xi) : ℂ := 1 - (starRingEnd ℂ) s.ρ

/-
  === The three true-analytic jet facts (parametric in the bridge instances) ===
-/

/-- Target 1: `w0At` is a quotient Jet3 window of `routeA_G s` at `z_w0At s`. -/
theorem jet_w0At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s (z_w0At s) (w0At m s)] :
    IsJet3AtOrderQuot m s (z_w0At s) (w0At m s) := by
  have hw : JetQuotRec2 s (padSeq3 (w0At m s)) :=
    rec2_w0At_trueAnalytic (m := m) (s := s)
  -- IMPORTANT: use the dedicated lemma (this is the stable API in your tree).
  simpa [z_w0At] using
    (TAC.isJet3AtOrderQuot_w0At_of_rec2 (m := m) (s := s) (z := z_w0At s) hw)

/-- Target 2: `wp2At` is a quotient Jet3 window of `routeA_G s` at `z_wp2At s`. -/
theorem jet_wp2At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s (z_wp2At s) (wp2At m s)] :
    IsJet3AtOrderQuot m s (z_wp2At s) (wp2At m s) := by
  have hw : JetQuotRec2 s (padSeq3 (wp2At m s)) :=
    rec2_wp2At_trueAnalytic (m := m) (s := s)
  simpa [z_wp2At] using
    (TAC.isJet3AtOrderQuot_wp2At_of_rec2 (m := m) (s := s) (z := z_wp2At s) hw)

/-- Target 3: `wp3At` is a quotient Jet3 window of `routeA_G s` at `z_wp3At s`. -/
theorem jet_wp3At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s (z_wp3At s) (wp3At m s)] :
    IsJet3AtOrderQuot m s (z_wp3At s) (wp3At m s) := by
  have hw : JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    rec2_wp3At_trueAnalytic (m := m) (s := s)
  simpa [z_wp3At] using
    (TAC.isJet3AtOrderQuot_wp3At_of_rec2 (m := m) (s := s) (z := z_wp3At s) hw)

end XiPacket
end Targets
end Hyperlocal
