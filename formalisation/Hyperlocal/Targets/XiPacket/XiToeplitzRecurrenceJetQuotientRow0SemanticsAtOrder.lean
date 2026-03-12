/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  Historical compatibility wrapper for the Row0 semantics surface.

  2026-03-13 honest post-axiom state:
  * the old global coords01 fallback provider has been removed
  * therefore this file can no longer rely on implicit synthesis of
      [XiJetQuotRec2AtOrderProvider]
    at an assumption-free surface
  * instead, this wrapper now re-exports the theorem-side endpoint under the
    honest gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]

  This is a compatibility wrapper in name only; the historical no-assumption
  ambient surface is no longer admissible after axiom removal.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder_Theorem

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

theorem xiJetQuotOpZeroAtOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotOpZeroAtOrder m s := by
  exact xiJetQuotOpZeroAtOrder_theorem (m := m) (s := s)

noncomputable def xiJetQuotRow0WitnessCAtOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow0WitnessCAtOrder m s := by
  exact xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
    (xiJetQuotOpZeroAtOrder (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
