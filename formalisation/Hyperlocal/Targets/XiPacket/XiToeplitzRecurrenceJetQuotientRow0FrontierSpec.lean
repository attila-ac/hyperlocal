/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpec.lean

  Thin public `wc` frontier seam.

  IMPORTANT:
  * keep this file minimal
  * do NOT import proof modules here
  * do NOT route this file through the new stencil corridor
  * this seam must stay acyclic
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

axiom xiJetQuot_row0_wc_spec
  (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0

end XiPacket
end Targets
end Hyperlocal
