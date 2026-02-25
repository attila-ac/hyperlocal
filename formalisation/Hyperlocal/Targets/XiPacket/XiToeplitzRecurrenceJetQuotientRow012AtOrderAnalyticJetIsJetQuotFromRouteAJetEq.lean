/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotFromRouteAJetEq.lean

  Route E payload (extractor-backed, NO new axioms).

  Provide a NON-CIRCULAR global source of quotient-jet facts for the three pivot windows:
      Hyperlocal.Targets.XiPacket.TAC.XiJetWindowIsJetAtOrderQuotProvider

  Key point:
  `ext` does not work for `ℂ` in this snapshot (no `[ext]` theorem registered),
  so we use `Complex.ext` explicitly.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-- Route E payload: install quotient-jet provider globally (extractor-backed). -/
instance : TAC.XiJetWindowIsJetAtOrderQuotProvider where
  jet_w0At := by
    intro m s

    -- Align the quot-provider anchor with Route–A's anchor.
    have hz : TAC.z_w0At s = s.ρ := by
      -- no `ext` for `ℂ` here; use `Complex.ext` directly
      apply Complex.ext
      · -- real part
        simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]
      · -- imag part
        simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]

    have hw : w0At m s = jet3 (routeA_G s) (TAC.z_w0At s) := by
      simpa [hz] using (w0At_eq_jet3_routeA (m := m) (s := s))

    have hj : IsJet3At (routeA_G s) (TAC.z_w0At s) (w0At m s) := by
      simpa [hw] using (isJet3At_jet3 (G := routeA_G s) (z := TAC.z_w0At s))

    simpa [IsJet3AtOrderQuot] using hj

  jet_wp2At := by
    intro m s
    have hj : IsJet3At (routeA_G s) (TAC.z_wp2At s) (wp2At m s) := by
      simpa [wp2At_eq_jet3_routeA, TAC.z_wp2At] using
        (isJet3At_jet3 (G := routeA_G s) (z := TAC.z_wp2At s))
    simpa [IsJet3AtOrderQuot] using hj

  jet_wp3At := by
    intro m s
    have hj : IsJet3At (routeA_G s) (TAC.z_wp3At s) (wp3At m s) := by
      simpa [wp3At_eq_jet3_routeA, TAC.z_wp3At] using
        (isJet3At_jet3 (G := routeA_G s) (z := TAC.z_wp3At s))
    simpa [IsJet3AtOrderQuot] using hj

end XiPacket
end Targets
end Hyperlocal
