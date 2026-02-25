/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticFromUpstream.lean

  Glue:
    [XiRow012UpstreamTrueAnalytic]
      ⇒ [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]

  This is cycle-safe: it only projects fields out of the existing
  theorem-level bundle `xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic`.
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
    XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by
  refine ⟨?_, ?_, ?_⟩
  · intro m s
    exact (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)).hw0At
  · intro m s
    exact (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)).hwp2At
  · intro m s
    exact (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)).hwp3At

end XiPacket
end Targets
end Hyperlocal
