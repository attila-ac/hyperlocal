/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream.lean

  Upstream proof for the Row0 frontier `wc` spec fact.

  CRITICAL:
  This file must NOT import anything that depends on:
    * XiToeplitzRecurrenceJetQuotientRow0Frontier
    * XiToeplitzRecurrenceJetQuotientRow0FrontierSpec
    * bridge/discharge stacks that re-import Row0Frontier
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtract

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiJetQuot_row0_wc_spec_proof (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using (xiJetQuotRow0ConcreteExtract (s := s)).hop_wc

end XiPacket
end Targets
end Hyperlocal
