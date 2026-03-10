/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpec.lean

  Historical public `wc` frontier surface.

  UPDATED POLICY:
  This is no longer an axiom declaration.
  It is now a theorem-backed wrapper around the new theorem-side stencil route.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

theorem xiJetQuot_row0_wc_spec
  (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using xiJetQuot_row0_wc_fromWcStencil (s := s)

end XiPacket
end Targets
end Hyperlocal
