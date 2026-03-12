/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticStripInterface.lean
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/-- Strip-specialised true-analytic upstream payload. -/
class XiRow012UpstreamTrueAnalyticStrip : Prop where
  row012_out_strip :
    ∀ (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi),
      XiRow012ConvolutionAtRevAtOrderOut m (s : OffSeed Xi)

end XiPacket
end Targets
end Hyperlocal
