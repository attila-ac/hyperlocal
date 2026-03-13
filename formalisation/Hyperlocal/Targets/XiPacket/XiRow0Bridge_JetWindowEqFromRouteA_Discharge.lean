/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Discharge.lean

  Legacy Route–A discharge surface.

  IMPORTANT (2026-03-13):
  * this legacy producer is now parameterized over `[RouteAWcCoordProvider]`
  * it no longer hardwires the residual `base` fallback into the full
    `RouteAJetCoordProvider` constant
  * any remaining fallback now sits strictly below this file
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderFromScalars
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_AtCoordsFromQuotJets

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

instance (priority := 900)
    [TAC.XiJetWindowIsJetAtOrderQuotProvider] [RouteAWcCoordProvider] :
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
    exact RouteAWcCoordProvider.wc_0 s

  · intro s
    exact RouteAWcCoordProvider.wc_1 s

  · intro s
    exact RouteAWcCoordProvider.wc_2 s

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
