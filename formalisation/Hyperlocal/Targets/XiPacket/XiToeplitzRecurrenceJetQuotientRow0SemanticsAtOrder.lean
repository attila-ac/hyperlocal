/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  Legacy ambient compatibility wrapper for the row0 semantics surface.

  IMPORTANT:
  * preserve the historical theorem/def names
  * keep the ambient-instance API surface for downstream compatibility
  * do NOT re-export the theorem-side true-analytic gate from here
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

theorem xiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  simpa using xiJetQuotOpZeroAtOrder_fromRecurrenceA (m := m) (s := s)

noncomputable def xiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  exact xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
    (xiJetQuotOpZeroAtOrder (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
