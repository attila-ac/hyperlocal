/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs.lean

  Cycle-safe definitions for the Row012 reverse-stencil payload bundle at order m.

  IMPORTANT:
    This file must contain ONLY defs/structures (no axioms, no theorems that depend
    on analytic extractors), so it can be imported from both sides without cycles.
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

end XiPacket
end Targets
end Hyperlocal
