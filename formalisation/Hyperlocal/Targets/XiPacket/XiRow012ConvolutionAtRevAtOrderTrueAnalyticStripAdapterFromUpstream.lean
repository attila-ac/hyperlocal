/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticStripAdapterFromUpstream.lean
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticStripInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalyticStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalyticStrip_compat
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m (s : OffSeed Xi) := by
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_strip
    (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
