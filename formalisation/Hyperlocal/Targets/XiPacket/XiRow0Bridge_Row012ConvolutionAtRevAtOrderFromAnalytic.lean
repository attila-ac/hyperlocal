/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic.lean

  Stable cycle-safe API endpoint:

    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic : XiRow012ConvolutionAtRevAtOrderOut m s

  This is a thin wrapper around the discharge file.
  It stays parametric in `[XiAtOrderSigmaProvider]` and *consumes* `[A0Nonzero]`
  via `infer_instance` (installed by `XiRow0Bridge_A0NonzeroBoundary`).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Discharge
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  classical
  letI : A0Nonzero (s := s) := by infer_instance
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
