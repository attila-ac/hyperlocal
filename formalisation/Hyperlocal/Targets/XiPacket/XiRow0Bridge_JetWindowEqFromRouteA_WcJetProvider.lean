/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcJetProvider.lean

  Upstream theorem/provider surface for the remaining `wc` Route-A jet fact.

  This is the right missing abstraction:
    instead of feeding `wc` coordinates from an axiom payload,
    we ask for the genuine jet statement

      IsJet3At (routeA_G s) (1 - s.ρ) (wc s)

  and project the three coordinates from it.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Upstream theorem surface for the missing `wc` Route-A jet fact.
-/
class RouteAWcJetProvider : Prop where
  jet_wc : ∀ s : OffSeed Xi, IsJet3At (routeA_G s) (1 - s.ρ) (wc s)

/-- Coordinate 0 projection from the upstream `wc` jet fact. -/
lemma wc_0_from_routeAWcJet
    (s : OffSeed Xi)
    [RouteAWcJetProvider] :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) := by
  have h := RouteAWcJetProvider.jet_wc (s := s)
  simpa using h.1

/-- Coordinate 1 projection from the upstream `wc` jet fact. -/
lemma wc_1_from_routeAWcJet
    (s : OffSeed Xi)
    [RouteAWcJetProvider] :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) := by
  have h := RouteAWcJetProvider.jet_wc (s := s)
  simpa using h.2.1

/-- Coordinate 2 projection from the upstream `wc` jet fact. -/
lemma wc_2_from_routeAWcJet
    (s : OffSeed Xi)
    [RouteAWcJetProvider] :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) := by
  have h := RouteAWcJetProvider.jet_wc (s := s)
  simpa using h.2.2

/--
Deterministic installation of the tiny coord provider from the upstream jet provider.
-/
instance (priority := 1000)
    [RouteAWcJetProvider] : RouteAWcCoordProvider where
  wc_0 := by
    intro s
    exact wc_0_from_routeAWcJet (s := s)
  wc_1 := by
    intro s
    exact wc_1_from_routeAWcJet (s := s)
  wc_2 := by
    intro s
    exact wc_2_from_routeAWcJet (s := s)

end XiPacket
end Targets
end Hyperlocal
