/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpec.lean

  Theorem-backed interface for Row0 frontier-at-order facts used downstream.

  POLICY:
  * keep the public `_spec` names stable
  * discharge them from the upstream proof lane
  * the upstream proof lane is theorem-gated after the post-axiom retarget
  * therefore this interface must expose the same honest gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport

theorem xiJetQuot_row0_w0At_spec
  (m : ℕ) (s : OffSeed Xi)
  [XiJetQuotRec2AtOrderTrueAnalytic]
  [TAC.XiJetWindowEqAtOrderQuotProvider] :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 := by
  exact xiJetQuot_row0_w0At_spec_proof (m := m) (s := s)

theorem xiJetQuot_row0_wp2At_spec
  (m : ℕ) (s : OffSeed Xi)
  [XiJetQuotRec2AtOrderTrueAnalytic]
  [TAC.XiJetWindowEqAtOrderQuotProvider] :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 := by
  exact xiJetQuot_row0_wp2At_spec_proof (m := m) (s := s)

theorem xiJetQuot_row0_wp3At_spec
  (m : ℕ) (s : OffSeed Xi)
  [XiJetQuotRec2AtOrderTrueAnalytic]
  [TAC.XiJetWindowEqAtOrderQuotProvider] :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 := by
  exact xiJetQuot_row0_wp3At_spec_proof (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
