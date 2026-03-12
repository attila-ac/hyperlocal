/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromTrueAnalytic.lean

  TRUE-ANALYTIC theorem wrapper for the AtOrder reverse-stencil Row012 bundle.

  Policy:
  * the implementation now routes through the strip-specialised Rec2 theorem lane
  * the global `OffSeed Xi` input is converted explicitly via the critical-strip bridge
  * the historical exported theorem name is preserved for downstream stability
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiTrueAnalyticCriticalStripBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

theorem xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  rcases hstrip : offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with ⟨hRe_pos, hRe_lt_one⟩
  let ss : _root_.Hyperlocal.OffSeedStrip Xi :=
    Hyperlocal.mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)
  have hs : ss.toOffSeed = s := by
    rfl
  simpa [ss, hs] using
    xiRow012ConvolutionAtRevAtOrderOut_fromRec2AtOrderTrueAnalytic_strip
      (m := m) (s := ss)

end XiPacket
end Targets
end Hyperlocal
