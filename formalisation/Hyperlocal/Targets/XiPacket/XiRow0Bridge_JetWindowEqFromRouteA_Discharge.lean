/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Discharge.lean

  Route–A discharge surface: provide a `RouteAJetCoordProvider`.

  IMPORTANT (2026-02-25+):
  * The AtOrder coordinates are now discharged theorem-level from quotient-jet facts.
  * The only remaining axioms in this file are the 12 *base-window* coordinate equalities
    (w0/wc/wp2/wp3 at coords 0/1/2).

  AXIOM COMPRESSION (2026-02-28):
  Replace those 12 separate axioms by ONE bundled axiom record, and keep the old
  names as theorem projections.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_AtCoordsFromQuotJets

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## Base-window axioms (remaining boundary in this file)

These are the only axioms left here: the 12 coordinate equalities for the base windows
`w0/wc/wp2/wp3` at coordinates 0/1/2.

AtOrder facts are *not* axiomatized here anymore.
-/

namespace RouteAJetCoordAxioms.Discharge

/-- Bundle the 12 base-window equalities into one object. -/
structure Base where
  w0_0  : ∀ s : OffSeed Xi, w0 s ⟨0, by decide⟩ = (routeA_G s) (s.ρ)
  w0_1  : ∀ s : OffSeed Xi, w0 s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ)
  w0_2  : ∀ s : OffSeed Xi, w0 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ)

  wc_0  : ∀ s : OffSeed Xi, wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ)
  wc_1  : ∀ s : OffSeed Xi, wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ)
  wc_2  : ∀ s : OffSeed Xi, wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ)

  wp2_0 : ∀ s : OffSeed Xi, wp2 s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ)
  wp2_1 : ∀ s : OffSeed Xi, wp2 s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ)
  wp2_2 : ∀ s : OffSeed Xi, wp2 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ)

  wp3_0 : ∀ s : OffSeed Xi, wp3 s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)
  wp3_1 : ∀ s : OffSeed Xi, wp3 s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)
  wp3_2 : ∀ s : OffSeed Xi, wp3 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ)

/-- The single base-window axiom payload. -/
axiom base : Base

theorem ax_w0_0  (s : OffSeed Xi) :
  w0 s ⟨0, by decide⟩ = (routeA_G s) (s.ρ) := base.w0_0 s
theorem ax_w0_1  (s : OffSeed Xi) :
  w0 s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ) := base.w0_1 s
theorem ax_w0_2  (s : OffSeed Xi) :
  w0 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ) := base.w0_2 s

theorem ax_wc_0  (s : OffSeed Xi) :
  wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) := base.wc_0 s
theorem ax_wc_1  (s : OffSeed Xi) :
  wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) := base.wc_1 s
theorem ax_wc_2  (s : OffSeed Xi) :
  wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) := base.wc_2 s

theorem ax_wp2_0 (s : OffSeed Xi) :
  wp2 s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ) := base.wp2_0 s
theorem ax_wp2_1 (s : OffSeed Xi) :
  wp2 s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ) := base.wp2_1 s
theorem ax_wp2_2 (s : OffSeed Xi) :
  wp2 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ) := base.wp2_2 s

theorem ax_wp3_0 (s : OffSeed Xi) :
  wp3 s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) := base.wp3_0 s
theorem ax_wp3_1 (s : OffSeed Xi) :
  wp3 s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) := base.wp3_1 s
theorem ax_wp3_2 (s : OffSeed Xi) :
  wp3 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ) := base.wp3_2 s

end RouteAJetCoordAxioms.Discharge

/-!
## Main instance: RouteAJetCoordProvider

* Base windows: from the bundled base axiom above.
* AtOrder windows: from quotient jets, via `RouteAJetCoordProviderAt` built from
  `[TAC.XiJetWindowIsJetAtOrderQuotProvider]`.
-/

instance (priority := 900)
    [TAC.XiJetWindowIsJetAtOrderQuotProvider] :
    RouteAJetCoordProvider := by
  classical
  haveI : RouteAJetCoordProviderAt := inferInstance

  refine
    { -- base windows (compressed axiom payload)
      w0_0  := RouteAJetCoordAxioms.Discharge.ax_w0_0
      w0_1  := RouteAJetCoordAxioms.Discharge.ax_w0_1
      w0_2  := RouteAJetCoordAxioms.Discharge.ax_w0_2

      wc_0  := RouteAJetCoordAxioms.Discharge.ax_wc_0
      wc_1  := RouteAJetCoordAxioms.Discharge.ax_wc_1
      wc_2  := RouteAJetCoordAxioms.Discharge.ax_wc_2

      wp2_0 := RouteAJetCoordAxioms.Discharge.ax_wp2_0
      wp2_1 := RouteAJetCoordAxioms.Discharge.ax_wp2_1
      wp2_2 := RouteAJetCoordAxioms.Discharge.ax_wp2_2

      wp3_0 := RouteAJetCoordAxioms.Discharge.ax_wp3_0
      wp3_1 := RouteAJetCoordAxioms.Discharge.ax_wp3_1
      wp3_2 := RouteAJetCoordAxioms.Discharge.ax_wp3_2

      -- AtOrder windows (theorem-level from quotient jets)
      w0At_0  := RouteAJetCoordProviderAt.w0At_0
      w0At_1  := RouteAJetCoordProviderAt.w0At_1
      w0At_2  := RouteAJetCoordProviderAt.w0At_2

      wp2At_0 := RouteAJetCoordProviderAt.wp2At_0
      wp2At_1 := RouteAJetCoordProviderAt.wp2At_1
      wp2At_2 := RouteAJetCoordProviderAt.wp2At_2

      wp3At_0 := RouteAJetCoordProviderAt.wp3At_0
      wp3At_1 := RouteAJetCoordProviderAt.wp3At_1
      wp3At_2 := RouteAJetCoordProviderAt.wp3At_2
    }

end XiPacket
end Targets
end Hyperlocal
