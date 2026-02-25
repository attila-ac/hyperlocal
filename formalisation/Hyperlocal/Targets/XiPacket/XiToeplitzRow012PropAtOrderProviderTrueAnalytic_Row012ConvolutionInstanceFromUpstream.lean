/-
  Provide the Row012 true-analytic class instance from the upstream analytic output.

  This is the missing glue:
    [XiRow012UpstreamTrueAnalytic] -> [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
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
    exact (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)).hw0At
  hwp2At := by
    intro m s
    exact (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)).hwp2At
  hwp3At := by
    intro m s
    exact (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)).hwp3At

end XiPacket
end Targets
end Hyperlocal
