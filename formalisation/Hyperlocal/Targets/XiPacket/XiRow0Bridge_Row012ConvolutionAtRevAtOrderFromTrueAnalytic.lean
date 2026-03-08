/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromTrueAnalytic.lean

  TRUE-ANALYTIC theorem wrapper for the AtOrder reverse-stencil Row012 bundle.

  Policy:
  * the implementation now runs through the Rec2-enabled theorem-side discharge lane
  * we keep the historical exported theorem name
      `xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic`
    for downstream stability
  * this file is theorem-level only
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalytic_Discharge
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Backwards-compatible theorem surface:

the historical exported name now delegates to the Rec2-enabled discharge lane.
-/
theorem xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  classical
  letI : XiAtOrderSigmaProvider := inferInstance
  letI : XiJetQuotRec2AtOrderProvider := inferInstance
  letI : A0Nonzero (s := s) := by infer_instance
  exact
    xiRow012ConvolutionAtRevAtOrderOut_fromRec2AtOrderTrueAnalytic_discharge
      (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
