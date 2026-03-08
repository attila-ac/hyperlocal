/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream.lean

  Import-surface repair for the true-analytic Row012 adapter.

  Policy:
  * this adapter remains the installed producer of `XiRow012UpstreamTrueAnalytic`
  * it re-exports the public theorem
      `xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic`
  * the required sigma producer is restored here explicitly
  * no local `haveI` patching
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem

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
