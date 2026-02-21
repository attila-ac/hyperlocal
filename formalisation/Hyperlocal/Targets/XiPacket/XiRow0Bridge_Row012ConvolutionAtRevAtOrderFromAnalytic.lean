/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic.lean

  Task A support (cycle-safe boundary for the analytic Row012 landing spot):

    Provide the Row012 reverse-convolution stencil payload for the three
    AtOrder windows `w0At/wp2At/wp3At` at their evaluation points.

  IMPORTANT:
    This file is intentionally *upstream* of the Row012 landing proof, and must
    not import any RecurrenceA / Row0Semantics modules.

  Status:
    This is the *current* admitted semantic boundary for the analytic chain.
    Once the true analytic discharge is completed, replace the axiom below by
    a theorem without changing the exported name.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeAtOrderRow012
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Prop bundle: row012 reverse-stencil payload for the three AtOrder windows. -/
structure XiRow012ConvolutionAtRevAtOrderOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : Row012ConvolutionAtRev s (s.ρ) (w0At m s)
  hwp2At : Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s)
  hwp3At : Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

/--
Cycle-safe admitted boundary: row012 stencil payload for AtOrder windows.

Replace this by the genuine analytic discharge after Task A is fully proven.
-/
axiom xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiRow012ConvolutionAtRevAtOrderOut m s

end XiPacket
end Targets
end Hyperlocal
