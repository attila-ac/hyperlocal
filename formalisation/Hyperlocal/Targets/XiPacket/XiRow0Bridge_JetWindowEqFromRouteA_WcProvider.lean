/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcProvider.lean

  Tiny provider surface for the three wc Route-A coordinate equalities.

  Purpose:
  isolate the remaining wc seam from the full RouteAJetCoordProvider builder.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Tiny theorem/provider surface for the `wc` Route-A coordinate triple only.

Keeping this separate lets the full `RouteAJetCoordProvider` builder stop
depending directly on the historical `Wc` axiom namespace.
-/
class RouteAWcCoordProvider : Prop where
  wc_0 : ∀ s : OffSeed Xi, wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ)
  wc_1 : ∀ s : OffSeed Xi, wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ)
  wc_2 : ∀ s : OffSeed Xi, wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ)

end XiPacket
end Targets
end Hyperlocal
