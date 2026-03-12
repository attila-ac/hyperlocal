/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow012UpstreamTrueAnalyticFromRec2TrueAnalyticStrip.lean

  Rec2-gated strip bridge:
    [XiJetQuotRec2AtOrderTrueAnalytic]
      ⇒ XiRow012UpstreamTrueAnalyticStrip
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticStripInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalyticStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

instance (priority := 900)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012UpstreamTrueAnalyticStrip where
  row012_out_strip := by
    intro m s
    simpa using
      (xiRow012ConvolutionAtRevAtOrderOut_fromRec2AtOrderTrueAnalytic_strip
        (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
