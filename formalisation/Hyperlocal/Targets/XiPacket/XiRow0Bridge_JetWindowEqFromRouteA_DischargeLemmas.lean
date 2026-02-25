/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_DischargeLemmas.lean

  REAL discharge surface for the missing “window = jet3” bridges, axiom-free.

  Design:
  * We do NOT unfold transport/toeplitz/shifts here.
  * We only use the canonicalizer lemma (in XiPacket.TAC):
        TAC.window_eq_jet3_routeA_of_isJet3AtOrderQuot
    which upgrades an `IsJet3AtOrderQuot` proof into an equality of windows.

  So the analytic/recurrence burden is pushed where it belongs:
  you prove `IsJet3AtOrderQuot` for your consumer windows, then these
  equalities follow immediately.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
-- ^ provides:
--   * Hyperlocal.Targets.XiPacket.TAC.jet3
--   * Hyperlocal.Targets.XiPacket.TAC.window_eq_jet3_routeA_of_isJet3AtOrderQuot

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Anchor for `w0At`: the Route–A point `ρ`. -/
@[simp] def z_w0At (s : OffSeed Xi) : ℂ := s.ρ

/-- Anchor for `wp2At`: the Route–A point `conj ρ`. -/
@[simp] def z_wp2At (s : OffSeed Xi) : ℂ := (starRingEnd ℂ) s.ρ

/-- Anchor for `wp3At`: the Route–A point `1 - conj ρ`. -/
@[simp] def z_wp3At (s : OffSeed Xi) : ℂ := (1 : ℂ) - (starRingEnd ℂ) s.ρ

/-
  === The three missing “window = jet3” bridges (axiom-free) ===
  Each one is one line once you have `IsJet3AtOrderQuot` for that window+anchor.
-/

/-- Discharge lemma 1: `w0At` equals the `jet3` window at `ρ`. -/
theorem w0At_eq_jet3_routeA
    (m : ℕ) (s : OffSeed Xi)
    (Hw : IsJet3AtOrderQuot m s (z_w0At s) (w0At m s)) :
    w0At m s = TAC.jet3 (routeA_G s) (z_w0At s) := by
  simpa using
    (TAC.window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := z_w0At s) (w := w0At m s) Hw)

/-- Discharge lemma 2: `wp2At` equals the `jet3` window at `conj ρ`. -/
theorem wp2At_eq_jet3_routeA
    (m : ℕ) (s : OffSeed Xi)
    (Hw : IsJet3AtOrderQuot m s (z_wp2At s) (wp2At m s)) :
    wp2At m s = TAC.jet3 (routeA_G s) (z_wp2At s) := by
  simpa using
    (TAC.window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := z_wp2At s) (w := wp2At m s) Hw)

/-- Discharge lemma 3: `wp3At` equals the `jet3` window at `1 - conj ρ`. -/
theorem wp3At_eq_jet3_routeA
    (m : ℕ) (s : OffSeed Xi)
    (Hw : IsJet3AtOrderQuot m s (z_wp3At s) (wp3At m s)) :
    wp3At m s = TAC.jet3 (routeA_G s) (z_wp3At s) := by
  simpa using
    (TAC.window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := z_wp3At s) (w := wp3At m s) Hw)

end XiPacket
end Targets
end Hyperlocal
