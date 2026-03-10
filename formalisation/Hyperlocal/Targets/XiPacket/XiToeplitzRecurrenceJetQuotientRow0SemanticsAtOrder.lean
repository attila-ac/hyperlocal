/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  Legacy ambient compatibility wrapper for the row0 semantics surface.

  IMPORTANT:
  * preserve the historical theorem/def names
  * keep the ambient-instance API surface for downstream compatibility
  * re-export the clean theorem-side row0 semantics
  * restore the needed theorem-provider surfaces explicitly by import
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

theorem xiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  simpa using xiJetQuotOpZeroAtOrder_theorem (m := m) (s := s)

noncomputable def xiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  simpa using xiJetQuotRow0WitnessCAtOrder_theorem (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
