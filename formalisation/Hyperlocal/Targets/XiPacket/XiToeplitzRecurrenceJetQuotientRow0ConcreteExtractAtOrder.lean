/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrder.lean

  Thin wrapper re-export for the AtOrder jet-quotient row-0 concrete extraction cliff.

  UPDATED POLICY:
  * this file now exports the theorem-only Route-B endpoint directly
  * it no longer imports the historical frontier wrapper
      `XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFrontier`
  * this keeps the public name stable while moving the live dependency path
    onto the theorem-level witness lane

  2026-03-13 honest post-axiom state:
  * the old global coords01 fallback provider has been removed
  * therefore this public wrapper can no longer remain assumption-free
  * it must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]

  NOTE (Lean 4.23):
  Since `XiJetQuotRow0ConcreteExtractAtOrder m s : Type`, the exported witness
  must be a `def` (not a `theorem`).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFromRecurrenceB
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/--
Type-level witness for the AtOrder concrete extraction cliff.

This now delegates directly to the theorem-level Route-B endpoint
`xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB`.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow0ConcreteExtractAtOrder m s :=
  xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB (m := m) (s := s)

/--
Prop-level packaged output derived from the Type-level concrete extract.
-/
theorem xiJetQuotRow0AtOrderOut_fromConcrete
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow0AtOrderOut m s := by
  exact
    xiJetQuotRow0AtOrderOut_of_extract (m := m) (s := s)
      (E := xiJetQuotRow0ConcreteExtractAtOrder (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
