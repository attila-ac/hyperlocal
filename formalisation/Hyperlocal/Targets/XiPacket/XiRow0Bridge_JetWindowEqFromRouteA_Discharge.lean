/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Discharge.lean

  Route–A discharge surface: provide a `RouteAJetCoordProvider`.

  IMPORTANT (2026-03-13):
  * the AtOrder coordinates are discharged theorem-level from quotient-jet facts
  * the base-window coordinates for `w0/wp2/wp3` are now also theorem-level,
    by specializing the same quotient-jet provider at `m = 0`
  * the only remaining fallback axiom is the residual `wc`-only payload in
      `XiRow0Bridge_JetWindowEqFromRouteA_BaseDischarge.lean`
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_BaseDischarge
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_AtCoordsFromQuotJets

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

instance (priority := 900)
    [TAC.XiJetWindowIsJetAtOrderQuotProvider] :
    RouteAJetCoordProvider := by
  classical
  haveI : RouteAJetCoordProviderAt := inferInstance

  refine
    {
      w0_0 := ?_, w0_1 := ?_, w0_2 := ?_
      wc_0 := ?_, wc_1 := ?_, wc_2 := ?_
      wp2_0 := ?_, wp2_1 := ?_, wp2_2 := ?_
      wp3_0 := ?_, wp3_1 := ?_, wp3_2 := ?_

      w0At_0 := RouteAJetCoordProviderAt.w0At_0
      w0At_1 := RouteAJetCoordProviderAt.w0At_1
      w0At_2 := RouteAJetCoordProviderAt.w0At_2

      wp2At_0 := RouteAJetCoordProviderAt.wp2At_0
      wp2At_1 := RouteAJetCoordProviderAt.wp2At_1
      wp2At_2 := RouteAJetCoordProviderAt.wp2At_2

      wp3At_0 := RouteAJetCoordProviderAt.wp3At_0
      wp3At_1 := RouteAJetCoordProviderAt.wp3At_1
      wp3At_2 := RouteAJetCoordProviderAt.wp3At_2
    }

  · intro s
    simpa [w0At_zero] using (RouteAJetCoordProviderAt.w0At_0 (m := 0) (s := s))

  · intro s
    simpa [w0At_zero] using (RouteAJetCoordProviderAt.w0At_1 (m := 0) (s := s))

  · intro s
    simpa [w0At_zero] using (RouteAJetCoordProviderAt.w0At_2 (m := 0) (s := s))

  · intro s
    exact RouteAJetCoordAxioms.Discharge.ax_wc_0 s

  · intro s
    exact RouteAJetCoordAxioms.Discharge.ax_wc_1 s

  · intro s
    exact RouteAJetCoordAxioms.Discharge.ax_wc_2 s

  · intro s
    simpa [wp2At_zero] using (RouteAJetCoordProviderAt.wp2At_0 (m := 0) (s := s))

  · intro s
    simpa [wp2At_zero] using (RouteAJetCoordProviderAt.wp2At_1 (m := 0) (s := s))

  · intro s
    simpa [wp2At_zero] using (RouteAJetCoordProviderAt.wp2At_2 (m := 0) (s := s))

  · intro s
    simpa [wp3At_zero] using (RouteAJetCoordProviderAt.wp3At_0 (m := 0) (s := s))

  · intro s
    simpa [wp3At_zero] using (RouteAJetCoordProviderAt.wp3At_1 (m := 0) (s := s))

  · intro s
    simpa [wp3At_zero] using (RouteAJetCoordProviderAt.wp3At_2 (m := 0) (s := s))

end XiPacket
end Targets
end Hyperlocal
