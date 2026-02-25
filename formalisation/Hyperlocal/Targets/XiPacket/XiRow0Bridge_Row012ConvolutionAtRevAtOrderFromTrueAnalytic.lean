/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromTrueAnalytic.lean

  TRUE-ANALYTIC endpoint (sigma-free in the *statement*):

    xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic :
      XiRow012ConvolutionAtRevAtOrderOut m s

  Implementation strategy (2026-02-25, updated E4/E5):
  We *do not* assume `[XiAtOrderSigmaProvider]` as an argument.
  Instead, we install a theorem-level sigma provider instance *locally* from the
  Prop-class recurrence gate:

      [XiJetQuotRec2AtOrderTrueAnalytic]
        ⇒ [XiJetQuotRec2AtOrderProvider]
        ⇒ XiJetQuotOpZeroAtOrder
        ⇒ row-0 ToeplitzL @ (0 : Fin 3)
        ⇒ row0Sigma via `toeplitzL_row0_eq_row0Sigma`
        ⇒ [XiAtOrderSigmaProvider]

  Then we reuse the existing discharge bundle (still written in terms of
  `[XiAtOrderSigmaProvider]`) to build the Row012 reverse-convolution payload.

  Achieved: removes dependency on the Route–B Row0 frontier-at-order projections.
  Still not manuscript-pure: it remains Rec2-gated (by design, this is on the RH critical path).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs

-- Frontier-free sigma provider derived from the Rec2 true-analytic interface.
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic

-- Existing discharge bundle (still written in terms of `[XiAtOrderSigmaProvider]`).
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Discharge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Sigma-free Row012 reverse-convolution payload at order.

NOTE:
This theorem is “sigma-free in the statement” by installing the sigma provider
instance locally from the Prop-class Rec2 gate (frontier-free).
-/
theorem xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  classical
  -- Ensure sigma is sourced from the Rec2 Prop-gate (not from any frontier shim).
  letI : XiAtOrderSigmaProvider := by infer_instance
  -- Reuse the existing discharge bundle.
  simpa using
    (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
