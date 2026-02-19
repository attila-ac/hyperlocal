/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateDefs.lean

  Cycle-safe defs-only layer for the AtOrder Gate.

  Contains ONLY the Prop-level bundled output structure
    `XiJetQuotRow0AtOrderConvolutionOut m s`
  with no axioms/theorems, so it is safe to import from analytic discharge files.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Route--C gate (Row--0 reverse convolution) for each AtOrder window. -/
structure XiJetQuotRow0AtOrderConvolutionOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : Row0ConvolutionAtRev s (s.ρ) (w0At m s)
  hwp2At : Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s)
  hwp3At : Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

end XiPacket
end Targets
end Hyperlocal
