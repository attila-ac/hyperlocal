/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms.lean

  Historical wc-only compatibility surface.

  IMPORTANT (2026-03-13):
  * this file is no longer an axiom boundary
  * keep the old theorem names `ax_wc_0/1/2` for compatibility
  * re-export them from the theorem-side wc bridge layer
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderFromScalars

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace RouteAJetCoordAxioms
namespace Wc

theorem ax_wc_0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) := by
  simpa using (JetQuotOp.routeA_G_wc_coord0 (s := s)).symm

theorem ax_wc_1
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) := by
  simpa using (JetQuotOp.routeA_G_wc_coord1 (s := s)).symm

theorem ax_wc_2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) := by
  simpa using (JetQuotOp.routeA_G_wc_coord2 (s := s)).symm

end Wc
end RouteAJetCoordAxioms

end XiPacket
end Targets
end Hyperlocal
