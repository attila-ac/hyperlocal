/-
  Provide the Row012 true-analytic concrete interface from the clean upstream
  payload class.

  Retarget:
    [XiRow012UpstreamTrueAnalytic] -> [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]

  IMPORTANT:
  This file must consume only the interface carrying
    `XiRow012UpstreamTrueAnalytic`
  and must NOT import the installed adapter surface.
  That was the SCC edge.

  This is a pure graph repair; no new mathematics.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
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
