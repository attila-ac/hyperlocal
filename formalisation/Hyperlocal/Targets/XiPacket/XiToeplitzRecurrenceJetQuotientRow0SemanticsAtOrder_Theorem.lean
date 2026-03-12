/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder_Theorem.lean

  Clean theorem-parametric AtOrder Route-B semantics surface.

  IMPORTANT:
  * this file is theorem-only
  * it does NOT import ambient provider installers
  * all required producer assumptions are explicit

  2026-03-12 correction:
  the upstream RecurrenceA theorem
      `xiJetQuotRec2AtOrder_fromRecurrenceA_theorem`
  now exposes the honest true-analytic gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]

  rather than ambient
      [XiAtOrderSigmaProvider]
      [XiAtOrderCoords01Provider].

  So this theorem-side row0 semantics surface must align to the same gate.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open scoped BigOperators
open Hyperlocal.Transport

theorem xiJetQuotOpZeroAtOrder_theorem
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotOpZeroAtOrder m s := by
  classical
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)
  exact xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec

noncomputable def xiJetQuotRow0WitnessCAtOrder_theorem
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow0WitnessCAtOrder m s := by
  exact xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
    (xiJetQuotOpZeroAtOrder_theorem (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
