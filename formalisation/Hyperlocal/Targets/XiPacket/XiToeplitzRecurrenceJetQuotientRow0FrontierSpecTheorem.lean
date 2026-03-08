/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpecTheorem.lean

  Theorem-backed version of the Row0 frontier `wc` spec fact.

  IMPORTANT:
  * This file is allowed to import the proof upstream module.
  * We do NOT touch the historical axiom surface yet (to avoid cycles).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

/-- Theorem-backed `wc` frontier spec fact. -/
theorem xiJetQuot_row0_wc_spec_theorem
  (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using xiJetQuot_row0_wc_spec_proof (s := s)

theorem xiJetQuot_row0_wc_spec' (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 :=
xiJetQuot_row0_wc_spec_theorem (s := s)

end XiPacket
end Targets
end Hyperlocal
