/-
  Provide the Row012 true-analytic concrete interface from the clean upstream
  Prop-class payload.

  Retarget:
    [XiRow012UpstreamTrueAnalytic] -> [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]

  IMPORTANT:
  This file must consume the upstream payload class directly, rather than calling
  the historical theorem
    `xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic`,
  because that theorem carries the legacy dirty cone.

  This is a consumer-side retarget only; no new mathematics.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

instance (priority := 850)
    [XiRow012UpstreamTrueAnalytic] :
    XiRow012ConvolutionAtRevAtOrderTrueAnalytic where
  hw0At := by
    intro m s
    exact (XiRow012UpstreamTrueAnalytic.row012_out (m := m) (s := s)).hw0At
  hwp2At := by
    intro m s
    exact (XiRow012UpstreamTrueAnalytic.row012_out (m := m) (s := s)).hwp2At
  hwp3At := by
    intro m s
    exact (XiRow012UpstreamTrueAnalytic.row012_out (m := m) (s := s)).hwp3At

end XiPacket
end Targets
end Hyperlocal
