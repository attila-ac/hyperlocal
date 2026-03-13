/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_BaseDischarge.lean

  Residual base-window Route-A fallback.

  IMPORTANT (2026-03-13):
  * after the theorem-side Route-A coord-provider cut, the only remaining
    non-AtOrder base-window fallback is the `wc` lane
  * the `w0/wp2/wp3` base-window coordinates are now discharged theoremically
    from the quotient-jet provider at `m = 0`
  * therefore this file keeps ONLY the three `wc` coordinate equalities
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace RouteAJetCoordAxioms.Discharge

/-- Residual `wc`-only fallback bundle. -/
structure Base where
  wc_0  : ∀ s : OffSeed Xi, wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ)
  wc_1  : ∀ s : OffSeed Xi, wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ)
  wc_2  : ∀ s : OffSeed Xi, wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ)

/-- The final residual Route-A fallback payload, now wc-only. -/
axiom base : Base

theorem ax_wc_0 (s : OffSeed Xi) :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) :=
  base.wc_0 s

theorem ax_wc_1 (s : OffSeed Xi) :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) :=
  base.wc_1 s

theorem ax_wc_2 (s : OffSeed Xi) :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) :=
  base.wc_2 s

end RouteAJetCoordAxioms.Discharge

end XiPacket
end Targets
end Hyperlocal
