/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalyticStrip.lean

  Strip-specialised theorem wrapper for the reverse-stencil Row012 bundle
  from the Rec2-at-order true-analytic corridor.

  2026-03-12 cleanup:
  the discharge theorem is now itself routed through the strip-specialised
  extra-lin lane, so this wrapper no longer needs to reinstall `A0Nonzero`.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalytic_Discharge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

theorem xiRow012ConvolutionAtRevAtOrderOut_fromRec2AtOrderTrueAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m (s : OffSeed Xi) := by
  let s0 : OffSeed Xi := (s : OffSeed Xi)
  simpa [s0] using
    (xiRow012ConvolutionAtRevAtOrderOut_fromRec2AtOrderTrueAnalytic_discharge
      (m := m) (s := s0))

end XiPacket
end Targets
end Hyperlocal
