/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpec.lean

  Axiom-thin interface for the Row0 frontier fact at `wc`.

  IMPORTANT:
  * This file must be minimal and must NOT import proof modules,
    otherwise it cycles through the bridge stack.
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
