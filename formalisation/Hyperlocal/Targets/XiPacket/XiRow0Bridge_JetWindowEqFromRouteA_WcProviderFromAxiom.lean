/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcProviderFromAxiom.lean

  Historical compatibility shim for the wc coord provider.

  IMPORTANT (2026-03-13):
  * no axiom payload remains here
  * keep this file only as a low-priority compatibility installer
  * the real live producer is theorem-side
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

instance (priority := 10)
    [TAC.XiJetWindowEqAtOrderQuotProvider] : RouteAWcCoordProvider where
  wc_0 := by
    intro s
    exact RouteAJetCoordAxioms.Wc.ax_wc_0 s
  wc_1 := by
    intro s
    exact RouteAJetCoordAxioms.Wc.ax_wc_1 s
  wc_2 := by
    intro s
    exact RouteAJetCoordAxioms.Wc.ax_wc_2 s

end XiPacket
end Targets
end Hyperlocal
