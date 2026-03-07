import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

def instRouteAProviderFromEq
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    RouteAJetCoordProvider := inferInstance

#print axioms instRouteAProviderFromEq
#print axioms RouteAJetCoordAxioms.Wc.ax_wc_0
#print axioms RouteAJetCoordAxioms.Wc.ax_wc_1
#print axioms RouteAJetCoordAxioms.Wc.ax_wc_2

end XiPacket
end Targets
end Hyperlocal
