/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream.lean

  Legacy ambient adapter for the Row012 true-analytic upstream surface.

  2026-03-12 / 2026-03-13:
  * keep the historical theorem name
  * keep the ambient sigma/coords compatibility wrapper
  * but route the proof through the cleaned analytic discharge endpoint

      xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic

  This is the last adapter/importer seam above the old coords01 fallback owner.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

theorem xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic_upstream
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider]
    [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
