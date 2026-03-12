/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream.lean

  Stable installed producer for `XiRow012UpstreamTrueAnalytic`.

  2026-03-12 retarget:
  * remove the legacy analytic endpoint route
  * do NOT reinstall `A0Nonzero`
  * consume the already-retargeted true-analytic theorem wrapper directly

  This keeps the historical installed surface

      [XiRow012UpstreamTrueAnalytic]

  while routing through

      xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic

  which itself now bridges
      OffSeed Xi -> OffSeedStrip Xi
  via the critical-strip bridge and delegates to the strip-specialised theorem corridor.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

instance (priority := 1000)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012UpstreamTrueAnalytic where
  row012_out := by
    intro m s
    simpa using
      (xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
