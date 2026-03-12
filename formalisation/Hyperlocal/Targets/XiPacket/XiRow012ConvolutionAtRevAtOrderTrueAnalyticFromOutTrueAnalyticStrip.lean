/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticFromOutTrueAnalyticStrip.lean

  Strip compatibility theorem:
    `XiRow012UpstreamTrueAnalyticStrip.row012_out_strip`
      -> bundled Row012 reverse-convolution output.

  IMPORTANT:
  This file does NOT install a new class instance.
  It only provides a theorem-level alias onto the canonical strip upstream bundle.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticStripInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiRow012UpstreamTrueAnalyticStrip] :
    XiRow012ConvolutionAtRevAtOrderOut m (s : OffSeed Xi) := by
  exact XiRow012UpstreamTrueAnalyticStrip.row012_out_strip (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
