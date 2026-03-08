/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream.lean

  Upstream proof for the Row0 frontier `wc` spec fact.

  IMPORTANT:
  This version avoids `XiToeplitzRecurrenceJetQuotientRow0ConcreteExtract`
  and instead uses the constructive scalar-goals witness route.

  Since `xiJetQuot_row0_scalarGoals` is provider-gated, this file must
  carry the same gate explicitly.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Analytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

theorem xiJetQuot_row0_wc_spec_proof (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  let g : XiJetQuotRow0ScalarGoals s := xiJetQuot_row0_scalarGoals (s := s)
  let h : _root_.Hyperlocal.Targets.XiPacket.XiJetQuotRow0WitnessC s :=
    witnessC_of_scalarGoals (s := s) g
  exact h.hop_wc

end XiPacket
end Targets
end Hyperlocal
