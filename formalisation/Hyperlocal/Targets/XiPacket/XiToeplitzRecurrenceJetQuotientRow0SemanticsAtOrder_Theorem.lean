/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder_Theorem.lean

  Clean theorem-parametric AtOrder Route-B semantics surface.

  IMPORTANT:
  * this file is theorem-only
  * it does NOT import ambient provider installers
  * all required producer assumptions are explicit
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

theorem xiJetQuotOpZeroAtOrder_theorem
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    XiJetQuotOpZeroAtOrder m s := by
  classical
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)
  exact xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec

noncomputable def xiJetQuotRow0WitnessCAtOrder_theorem
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    XiJetQuotRow0WitnessCAtOrder m s := by
  exact xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
    (xiJetQuotOpZeroAtOrder_theorem (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
