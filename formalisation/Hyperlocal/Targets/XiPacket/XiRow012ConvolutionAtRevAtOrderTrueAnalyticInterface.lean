/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface.lean

  Serious analytic discharge interface (B) (Prop-first):

    class XiRow012UpstreamTrueAnalytic : Prop :=
      row012_out : ∀ m s, XiRow012ConvolutionAtRevAtOrderOut m s

  This keeps the remaining cliff as:
    "prove the tail-gate convolution payload bundle"
  and leaves all downstream Prop⇒Type packaging to existing theorem-level bridges.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- True-analytic upstream payload: the tail-gate convolution bundle at order (Prop-first). -/
class XiRow012UpstreamTrueAnalytic : Prop :=
  (row012_out : ∀ (m : ℕ) (s : OffSeed Xi), XiRow012ConvolutionAtRevAtOrderOut m s)

end XiPacket
end Targets
end Hyperlocal
