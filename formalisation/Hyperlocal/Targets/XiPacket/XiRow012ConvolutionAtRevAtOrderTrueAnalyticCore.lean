/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticCore.lean

  TRUE-ANALYTIC *core* interface for the Row012 reverse-stencil convolution facts.

  IMPORTANT:
  * This file is intentionally **Rec2-free**.
  * It should import only the Row012 convolution definition and the canonical pivot windows.

  The downstream chain is:

    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
        ⇒ [XiToeplitzRow012PropAtOrderTrueAnalytic]
        ⇒ ... (Rec2 etc., in separate files)
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
True-analytic Row012 reverse-stencil convolution gate (sigma-free).

This is *exactly* the analytic content that should come from the manuscript stack
(FE/RC/factorisation/Route-A, etc.).
-/
class XiRow012ConvolutionAtRevAtOrderTrueAnalytic : Prop where
  hw0At  :
    ∀ (m : ℕ) (s : OffSeed Xi),
      Row012ConvolutionAtRev s s.ρ (w0At m s)
  hwp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s)
  hwp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

end XiPacket
end Targets
end Hyperlocal
