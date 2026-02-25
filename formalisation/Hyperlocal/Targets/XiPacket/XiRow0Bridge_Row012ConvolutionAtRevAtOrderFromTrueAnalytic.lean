/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromTrueAnalytic.lean

  TRUE-ANALYTIC endpoint (sigma-free in the *statement*):

    xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic :
      XiRow012ConvolutionAtRevAtOrderOut m s

  Implementation strategy (2026-02-25):
  We *do not* assume `[XiAtOrderSigmaProvider]` as an argument.
  Instead, we install the theorem-level sigma provider instance derived from the
  existing Route–B Row0 frontier-at-order projections, and then reuse the existing
  discharge bundle that builds the Row012 reverse-convolution payload.

  This is the minimal “no-sorry, no-renaming” bridge that keeps downstream
  Prop-first Row012 packaging moving toward unconditional RH without refactors.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs

-- Theorem-level sigma provider derived from the Route–B Row0 frontier at order.
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder

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
instance locally (derived from the Route–B frontier).
-/
theorem xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  classical
  -- Install the theorem-level sigma provider instance (from the Row0 frontier).
  letI : XiAtOrderSigmaProvider := by infer_instance
  -- Reuse the existing discharge bundle.
  simpa using
    (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
