/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrder.lean

  Thin wrapper re-export for the AtOrder jet-quotient row-0 concrete extraction cliff.

  Policy:
  * The ONLY axiom is in `...AtOrderFrontier.lean`.
  * This file exposes stable downstream-facing names, without importing any
    Row0Correctness/Bridge layers.

  NOTE (Lean 4.23):
  Since `XiJetQuotRow0ConcreteExtractAtOrder m s : Type`, the exported witness
  must be a `def` (not a `theorem`).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFrontier

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Type-level witness for the AtOrder concrete extraction cliff.

Currently delegates to the single frontier axiom.
When the frontier axiom is replaced by a theorem, this definition stays unchanged.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s :=
  xiJetQuotRow0ConcreteExtractAtOrder_frontier m s

/--
Prop-level packaged output derived from the Type-level concrete extract.

This is what the AtOrder frontier projections use.
-/
theorem xiJetQuotRow0AtOrderOut_fromConcrete (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0AtOrderOut m s := by
  exact
    xiJetQuotRow0AtOrderOut_of_extract (m := m) (s := s)
      (E := xiJetQuotRow0ConcreteExtractAtOrder (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
