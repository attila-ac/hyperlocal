/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream.lean

  Upstream proofs for the Row0 frontier *AtOrder* spec facts.

  IMPORTANT:
  This file MUST be upstream-only: it imports the real frontier-at-order theorem module
  and exports `_spec_proof` lemmas for spec surfaces to alias.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiJetQuot_row0_w0At_spec_proof
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 :=
  xiJetQuot_row0_w0At (m := m) (s := s)

theorem xiJetQuot_row0_wp2At_spec_proof
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
  xiJetQuot_row0_wp2At (m := m) (s := s)

theorem xiJetQuot_row0_wp3At_spec_proof
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
  xiJetQuot_row0_wp3At (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
