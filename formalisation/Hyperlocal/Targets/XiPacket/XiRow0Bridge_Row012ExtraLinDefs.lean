/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinDefs.lean

  Cycle-safe definition of the two extra linear constraints needed to upgrade
  Row0ConvolutionAtRev -> Row012ConvolutionAtRev via the closed forms of convCoeff 4/5.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- The two extra linear constraints corresponding to reverse convCoeff 4 and 5. -/
structure Row012ExtraLin (s : OffSeed Xi) (w : Window 3) : Prop where
  h4 : (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0
  h5 : (-2 : ℂ) * (w 0) = 0

namespace Row012ExtraLinDefsExport
export _root_.Hyperlocal.Targets.XiPacket (Row012ExtraLin)
end Row012ExtraLinDefsExport

end XiPacket
end Targets
end Hyperlocal
