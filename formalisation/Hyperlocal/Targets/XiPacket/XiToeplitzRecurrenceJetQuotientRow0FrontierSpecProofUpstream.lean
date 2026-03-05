/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream.lean

  Upstream proof for the Row0 frontier `wc` spec fact.

  IMPORTANT:
  This file MUST NOT import any `_Spec.lean` surface modules.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischarge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiJetQuot_row0_wc_spec_proof (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  -- stable theorem exported by the analytic/bridge side:
  have hσ : row0Sigma s (wc s) = 0 :=
    _root_.Hyperlocal.Targets.XiPacket.row0Sigma_wc_eq_zero s
  simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wc s)] using hσ

end XiPacket
end Targets
end Hyperlocal
