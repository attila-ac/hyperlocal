import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

theorem xiJetQuot_row0_w0At_spec_proof
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 := by
  classical
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream (m := m) (s := s)
  simpa using Hw.hop_w0At

theorem xiJetQuot_row0_wp2At_spec_proof
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 := by
  classical
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream (m := m) (s := s)
  simpa using Hw.hop_wp2At

theorem xiJetQuot_row0_wp3At_spec_proof
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 := by
  classical
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream (m := m) (s := s)
  simpa using Hw.hop_wp3At

end XiPacket
end Targets
end Hyperlocal
