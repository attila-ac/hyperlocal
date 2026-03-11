/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcProviderFromAxiom.lean

  Temporary installer of the tiny wc provider from the historical wc axiom lane.
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

instance (priority := 1000) : RouteAWcCoordProvider where
  wc_0 := by
    intro s
    simpa using RouteAJetCoordAxioms.Wc.ax_wc_0 s
  wc_1 := by
    intro s
    simpa using RouteAJetCoordAxioms.Wc.ax_wc_1 s
  wc_2 := by
    intro s
    simpa using RouteAJetCoordAxioms.Wc.ax_wc_2 s

end XiPacket
end Targets
end Hyperlocal
