/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Concrete.lean
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

theorem xiJetQuot_row0_w0 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
  simpa using xiJetQuot_row0_w0_fromWcStencil (s := s)

theorem xiJetQuot_row0_wc (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using xiJetQuot_row0_wc_fromWcStencil (s := s)

theorem xiJetQuot_row0_wp2 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
  simpa using xiJetQuot_row0_wp2_fromWcStencil (s := s)

theorem xiJetQuot_row0_wp3 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 := by
  simpa using xiJetQuot_row0_wp3_fromWcStencil (s := s)

end XiPacket
end Targets
end Hyperlocal
