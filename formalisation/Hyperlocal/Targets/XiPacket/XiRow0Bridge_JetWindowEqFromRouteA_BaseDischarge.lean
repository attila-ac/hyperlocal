/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_BaseDischarge.lean

  Residual base-window Route-A compatibility surface.

  IMPORTANT (2026-03-13):
  * this file is no longer an axiom boundary
  * the residual `wc` base-window equalities are now re-exported from the
    theorem-side `wc` bridge layer
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace RouteAJetCoordAxioms.Discharge

theorem ax_wc_0
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) :=
  RouteAJetCoordAxioms.Wc.ax_wc_0 s

theorem ax_wc_1
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) :=
  RouteAJetCoordAxioms.Wc.ax_wc_1 s

theorem ax_wc_2
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) :=
  RouteAJetCoordAxioms.Wc.ax_wc_2 s

end RouteAJetCoordAxioms.Discharge

end XiPacket
end Targets
end Hyperlocal
