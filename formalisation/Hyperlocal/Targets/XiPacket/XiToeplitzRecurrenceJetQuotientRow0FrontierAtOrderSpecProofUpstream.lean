/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream.lean

  Upstream proofs for the Row0 frontier *AtOrder* spec facts.

  UPDATED POLICY:
  * consume the packaged theorem-level concrete-extract output directly
  * do NOT import the historical frontier theorem wrapper
  * keep the `_spec_proof` names stable for downstream theorem lanes
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiJetQuot_row0_w0At_spec_proof
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0AtOrderOut_fromConcrete m s).hw0At

theorem xiJetQuot_row0_wp2At_spec_proof
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0AtOrderOut_fromConcrete m s).hwp2At

theorem xiJetQuot_row0_wp3At_spec_proof
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0AtOrderOut_fromConcrete m s).hwp3At

end XiPacket
end Targets
end Hyperlocal
