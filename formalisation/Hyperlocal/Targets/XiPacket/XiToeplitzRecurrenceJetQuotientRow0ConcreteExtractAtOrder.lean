/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrder.lean

  Thin wrapper re-export for the AtOrder jet-quotient row-0 concrete extraction cliff.

  Policy:
  * The ONLY axiom is in `...AtOrderFrontier.lean`.
  * This file exposes a Type-level name (`def`) that downstream imports can use
    without touching the frontier module directly.
  * Prop-level packaging remains theorem-level.

  When the frontier axiom is discharged (replaced by a theorem/def),
  this file becomes entirely axiom-free without downstream edits.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFrontier

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Type-level name for the AtOrder concrete extraction witness.

Currently delegates to the single frontier axiom.
Once the frontier is discharged, this becomes a definitional alias to that proof.
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
