/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticStripAdapterFromUpstream.lean

  Compatibility theorem for the strip analytic endpoint.

  IMPORTANT:
  * this file no longer installs an instance for
      `XiRow012UpstreamTrueAnalyticStrip`
  * the canonical installed producer now lives in
      `XiRow012UpstreamTrueAnalyticFromRec2TrueAnalyticStrip.lean`
  * keep this file theorem-only to avoid duplicate strip-upstream producers
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

/--
Compatibility theorem exposing the strip analytic Row012 bundle directly,
without installing a second strip-upstream instance.
-/
theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalyticStrip_compat
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m (s : OffSeed Xi) := by
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_strip
    (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
