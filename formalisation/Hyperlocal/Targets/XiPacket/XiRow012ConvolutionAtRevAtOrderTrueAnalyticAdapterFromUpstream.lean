/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream.lean

  Stable installed producer for `XiRow012UpstreamTrueAnalytic`.

  IMPORTANT:
  * this file is an installer root
  * therefore it must use producer surfaces that are already available here
  * do NOT import `XiRow0Bridge_AtOrderCoords01ProviderTheorem` here
    because that re-enters the analytic extractor cone and creates a build cycle

  Policy:
  * remain the installed producer of `XiRow012UpstreamTrueAnalytic`
  * re-export `xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic`
  * use the stable theorem-backed sigma producer
  * use the stable fallback coords01 installer surface
  * no local `haveI` patching
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

instance (priority := 1000) : XiRow012UpstreamTrueAnalytic where
  row012_out := by
    intro m s
    exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
