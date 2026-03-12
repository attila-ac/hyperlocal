/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalyticStrip.lean

  Strip-specialised theorem wrapper for the reverse-stencil Row012 bundle
  from the Rec2-at-order true-analytic corridor.
-/

import Hyperlocal.Transport.OffSeedStrip

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalytic_Discharge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip

-- canonical producer surfaces for the two inferred instances below
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic

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
  classical
  let s0 : OffSeed Xi := (s : OffSeed Xi)

  letI : XiAtOrderSigmaProvider := inferInstance
  letI : XiJetQuotRec2AtOrderProvider := inferInstance
  letI : A0Nonzero (s := s0) := ⟨by
    simpa [s0] using (a0_ne_zero_of_strip (s := s))
  ⟩

  simpa [s0] using
    (xiRow012ConvolutionAtRevAtOrderOut_fromRec2AtOrderTrueAnalytic_discharge
      (m := m) (s := s0))

end XiPacket
end Targets
end Hyperlocal
