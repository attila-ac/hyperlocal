/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetFromTrueAnalytic.lean

  Option B (quotient jets):
    Provide the three jet predicates for the Route-A quotient model `routeA_G s`
    at the three Row012 anchors.

  This avoids trying to identify the Row012 witness `G` with `cderivIter m Xi`
  (which is not available from the current Row012 payload).
-/

import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA
import Hyperlocal.Targets.XiPacket.XiJet3Defs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC

/-
  Local anchor abbreviations.

  IMPORTANT:
  We define these exactly to match the centers used by the Route-A bridge axioms:
    w0At at s.ρ
    wp2At at (starRingEnd ℂ) s.ρ
    wp3At at 1 - (starRingEnd ℂ) s.ρ

  This keeps this file self-contained (no dependency on the older `sc/delta` transport anchors).
-/
def z_w0At (s : OffSeed Xi) : ℂ := s.ρ
def z_wp2At (s : OffSeed Xi) : ℂ := (starRingEnd ℂ) s.ρ
def z_wp3At (s : OffSeed Xi) : ℂ := 1 - (starRingEnd ℂ) s.ρ

/-- Parallel provider for the *quotient* jet notion `IsJet3AtOrderQuot`. -/
class XiJetWindowIsJetAtOrderQuotProvider : Prop where
  jet_w0At  : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s (z_w0At s) (w0At m s)
  jet_wp2At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s (z_wp2At s) (wp2At m s)
  jet_wp3At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s (z_wp3At s) (wp3At m s)

/-- Convenience: Jet3 tautology (binder name is `G`). -/
private lemma isJet3At_jet3_apply (G : ℂ → ℂ) (z : ℂ) :
    IsJet3At G z (jet3 G z) := by
  simpa using (isJet3At_jet3 (G := G) (z := z))

/-- Target 1: `w0At` is the Jet3 window of `routeA_G s` at `z_w0At s`. -/
theorem jet_w0At_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrderQuot m s (z_w0At s) (w0At m s) := by
  classical
  have hw : w0At m s = jet3 (routeA_G s) (s.ρ) :=
    w0At_eq_jet3_routeA (m := m) (s := s)

  have hj :
      IsJet3At (routeA_G s) (s.ρ) (jet3 (routeA_G s) (s.ρ)) :=
    isJet3At_jet3_apply (routeA_G s) (s.ρ)

  -- `z_w0At s` is definitional `s.ρ`.
  simpa [IsJet3AtOrderQuot, z_w0At, hw] using hj

/-- Target 2: `wp2At` is the Jet3 window of `routeA_G s` at `z_wp2At s`. -/
theorem jet_wp2At_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrderQuot m s (z_wp2At s) (wp2At m s) := by
  classical
  have hw : wp2At m s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
    wp2At_eq_jet3_routeA (m := m) (s := s)

  have hj :
      IsJet3At (routeA_G s) ((starRingEnd ℂ) s.ρ)
        (jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ)) :=
    isJet3At_jet3_apply (routeA_G s) ((starRingEnd ℂ) s.ρ)

  simpa [IsJet3AtOrderQuot, z_wp2At, hw] using hj

/-- Target 3: `wp3At` is the Jet3 window of `routeA_G s` at `z_wp3At s`. -/
theorem jet_wp3At_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrderQuot m s (z_wp3At s) (wp3At m s) := by
  classical
  have hw : wp3At m s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
    wp3At_eq_jet3_routeA (m := m) (s := s)

  have hj :
      IsJet3At (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)
        (jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)) :=
    isJet3At_jet3_apply (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)

  simpa [IsJet3AtOrderQuot, z_wp3At, hw] using hj

/-- Install the quotient-jet provider. -/
instance : XiJetWindowIsJetAtOrderQuotProvider where
  jet_w0At  := jet_w0At_fromTrueAnalytic
  jet_wp2At := jet_wp2At_fromTrueAnalytic
  jet_wp3At := jet_wp3At_fromTrueAnalytic

end TAC

end XiPacket
end Targets
end Hyperlocal
