/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms.lean

  Tiny wc-only axiom surface for the Route-A jet-window coordinates.

  Purpose:
  * shrink the old bundled RouteA provider boundary
  * isolate the remaining dirty edge to the three `wc` coordinate equalities
  * allow theorem-backed installation of all other RouteA fields

  This file should contain ONLY the `wc` coordinate boundary.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace RouteAJetCoordAxioms
namespace Wc

/-- Tiny bundled axiom payload for the three `wc` Route-A coordinates. -/
structure Payload where
  wc_0 : ∀ s : OffSeed Xi, wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ)
  wc_1 : ∀ s : OffSeed Xi, wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ)
  wc_2 : ∀ s : OffSeed Xi, wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ)

/-- The only remaining wc-only axiom payload. -/
axiom payload : Payload

theorem ax_wc_0 (s : OffSeed Xi) :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) :=
  payload.wc_0 s

theorem ax_wc_1 (s : OffSeed Xi) :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) :=
  payload.wc_1 s

theorem ax_wc_2 (s : OffSeed Xi) :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) :=
  payload.wc_2 s

end Wc
end RouteAJetCoordAxioms

end XiPacket
end Targets
end Hyperlocal
