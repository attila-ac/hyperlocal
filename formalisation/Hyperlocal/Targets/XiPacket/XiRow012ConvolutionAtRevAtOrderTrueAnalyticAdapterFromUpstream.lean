/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream.lean

  Stable installed producer for `XiRow012UpstreamTrueAnalytic`.

  IMPORTANT:
  * this file is an installer root
  * therefore it must use producer surfaces that are already available here
  * do NOT import the analytic sigma surface here, because that route is conditional on
      `[XiJetQuotRec2AtOrderTrueAnalytic]`
    and that premise is not available at this installer boundary

  Policy:
  * remain the installed producer of `XiRow012UpstreamTrueAnalytic`
  * re-export `xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic`
  * use the stable theorem-backed sigma/coords producer surfaces here
  * no local `haveI` patching
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem

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
