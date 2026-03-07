/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotFromRouteAJetEq.lean

  Route E payload (extractor-backed, NO new axioms).

  Bridge theorem-side quotient-window equalities to theorem-side quotient-jet facts:

      TAC.XiJetWindowEqAtOrderQuotProvider
          ⇒
      TAC.XiJetWindowIsJetAtOrderQuotProvider

  IMPORTANT:
  This file is not a root producer.  It is a bridge layer.
  Therefore the required Eq-provider must be stated explicitly.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Theorem

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

/--
Bridge Eq-provider facts to IsJet-provider facts.

This is theorem-side only:
it assumes `[TAC.XiJetWindowEqAtOrderQuotProvider]`
and produces `[TAC.XiJetWindowIsJetAtOrderQuotProvider]`.
-/
instance (priority := 1000)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    TAC.XiJetWindowIsJetAtOrderQuotProvider where
  jet_w0At := by
    intro m s

    have hz : TAC.z_w0At s = s.ρ := by
      apply Complex.ext
      · simp [TAC.z_w0At, sc, t, Hyperlocal.Targets.XiTransport.delta]
      · simp [TAC.z_w0At, sc, t, Hyperlocal.Targets.XiTransport.delta]

    have hw : w0At m s = jet3 (routeA_G s) (TAC.z_w0At s) := by
      simpa [hz] using (w0At_eq_jet3_routeA (m := m) (s := s))

    have hj : IsJet3At (routeA_G s) (TAC.z_w0At s) (w0At m s) := by
      simpa [hw] using
        (isJet3At_jet3 (G := routeA_G s) (z := TAC.z_w0At s))

    simpa [IsJet3AtOrderQuot] using hj

  jet_wp2At := by
    intro m s

    have hw : wp2At m s = jet3 (routeA_G s) (TAC.z_wp2At s) := by
      simpa [TAC.z_wp2At] using
        (wp2At_eq_jet3_routeA (m := m) (s := s))

    have hj : IsJet3At (routeA_G s) (TAC.z_wp2At s) (wp2At m s) := by
      simpa [hw] using
        (isJet3At_jet3 (G := routeA_G s) (z := TAC.z_wp2At s))

    simpa [IsJet3AtOrderQuot] using hj

  jet_wp3At := by
    intro m s

    have hw : wp3At m s = jet3 (routeA_G s) (TAC.z_wp3At s) := by
      simpa [TAC.z_wp3At] using
        (wp3At_eq_jet3_routeA (m := m) (s := s))

    have hj : IsJet3At (routeA_G s) (TAC.z_wp3At s) (wp3At m s) := by
      simpa [hw] using
        (isJet3At_jet3 (G := routeA_G s) (z := TAC.z_wp3At s))

    simpa [IsJet3AtOrderQuot] using hj

end XiPacket
end Targets
end Hyperlocal
