/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderFromScalars.lean

  Upstream theorem-side installer for the `wc` jet provider, reduced to the
  three scalar Route-A normalization coordinates at `1 - s.ρ`.

  IMPORTANT:
  * this file must stay acyclic
  * in particular, it must NOT import
      `XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem`
    because that theorem wrapper already depends on the theorem-side
    Route-A window-equality surface, whose live producer depends back on
    the `wc` provider installed here.

  Therefore we rebuild only the tiny raw Route-A analytic package locally
  from:
    * `routeA_G`
    * `jet3`
    * analytic discharge lemmas

  Honest frontier:
    * `wc` is already the concrete target window
    * so we avoid any fake window-coordinate helper lemmas here
    * the remaining work is exactly the three coordinate equalities below
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
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

namespace JetQuotOp

/--
Local raw Route-A jet package at the canonical jet window.

This is intentionally duplicated here in minimal form so that the `wc`
provider installer does not import the theorem wrapper
`XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem`, which would create an
import cycle through the theorem-side coord-provider surface.
-/
private theorem xiRouteA_jetPkg_jet3_local
    (s : OffSeed Xi) (z : ℂ) :
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 (routeA_G s) ∧
    IsJet3At (routeA_G s) z (jet3 (routeA_G s) z) ∧
    Differentiable ℂ (Rfun s) ∧
    Differentiable ℂ (routeA_G s) ∧
    Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
    Differentiable ℂ (fun t => deriv (routeA_G s) t) := by
  classical
  refine ⟨routeA_G_factorised s, ?_, ?_, ?_, ?_, ?_⟩
  · exact isJet3At_jet3 (routeA_G s) z
  · exact Rfun_differentiable s
  · exact G_differentiable_of_entire (routeA_G_entire s)
  · exact Rfun_deriv_differentiable s
  · exact G_deriv_differentiable_of_entire (routeA_G_entire s)

/--
Coordinate 0 bridge at `z = 1 - s.ρ`.

This is the value-side normalization, stated directly against the concrete
target window `wc s`.
-/
theorem routeA_G_wc_coord0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    (routeA_G s) (1 - s.ρ) = wc s (0 : Fin 3) := by
  classical
  have H := xiRouteA_jetPkg_jet3_local (s := s) (z := (1 - s.ρ))
  rcases H with ⟨_, hjet, _, _, _, _⟩
  /-
    Frontier seam:
    convert the raw canonical jet witness `hjet`
    into the concrete definitional window `wc s`,
    upstream and non-circularly.
  -/
  sorry

/--
Coordinate 1 bridge at `z = 1 - s.ρ`.

This is the first-derivative normalization, stated directly against `wc s`.
-/
theorem routeA_G_wc_coord1
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    deriv (routeA_G s) (1 - s.ρ) = wc s (1 : Fin 3) := by
  classical
  have H := xiRouteA_jetPkg_jet3_local (s := s) (z := (1 - s.ρ))
  rcases H with ⟨_, hjet, _, _, _, _⟩
  /-
    Same frontier seam as coord0, but for the first derivative coordinate.
  -/
  sorry

/--
Coordinate 2 bridge at `z = 1 - s.ρ`.

This is the second-derivative normalization, stated directly against `wc s`.
-/
theorem routeA_G_wc_coord2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    deriv (deriv (routeA_G s)) (1 - s.ρ) = wc s (2 : Fin 3) := by
  classical
  have H := xiRouteA_jetPkg_jet3_local (s := s) (z := (1 - s.ρ))
  rcases H with ⟨_, hjet, _, _, _, _⟩
  /-
    Same frontier seam as coord0/coord1, but for the second derivative coordinate.
  -/
  sorry

/--
Assemble the three scalar coordinate bridges into the upstream `wc` jet fact.
-/
theorem wc_isJet3At_routeA
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    IsJet3At (routeA_G s) (1 - s.ρ) (wc s) := by
  constructor
  · symm
    exact routeA_G_wc_coord0 (s := s)
  constructor
  · symm
    exact routeA_G_wc_coord1 (s := s)
  · symm
    exact routeA_G_wc_coord2 (s := s)

/--
Install the upstream `wc` jet provider from the scalar bridge layer.
-/
instance (priority := 1000)
    [TAC.XiJetWindowEqAtOrderQuotProvider] : RouteAWcJetProvider where
  jet_wc := by
    intro s
    exact wc_isJet3At_routeA (s := s)

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
