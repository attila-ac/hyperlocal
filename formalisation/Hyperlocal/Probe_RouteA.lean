import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Core
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider

def instRouteAProvider :
    Hyperlocal.Targets.XiPacket.RouteAJetCoordProvider := inferInstance

#print axioms instRouteAProvider
#print axioms Hyperlocal.Targets.XiPacket.w0_eq_jet3_routeA
#print axioms Hyperlocal.Targets.XiPacket.wc_eq_jet3_routeA
