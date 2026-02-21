/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic.lean

  Stable cycle-safe API endpoint:

    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic : XiRow012ConvolutionAtRevAtOrderOut m s
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Discharge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiRow012ConvolutionAtRevAtOrderOut m s :=
  xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
