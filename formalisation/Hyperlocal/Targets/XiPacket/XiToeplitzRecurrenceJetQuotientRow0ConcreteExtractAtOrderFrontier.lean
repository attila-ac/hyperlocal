/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFrontier.lean

  SINGLE semantic frontier (AtOrder): this is the one remaining axiom for the
  jet-pivot row-0 jet-quotient recurrence extraction layer.

  Replace the axiom in this file by a theorem once the concrete order-`m`
  recurrence extraction theorem is formalised.

  No other file should introduce axioms for this AtOrder endpoint.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
SINGLE semantic frontier (AtOrder): the concrete ξ jet-quotient recurrence
extraction theorem should provide this Type-level witness.
-/
axiom xiJetQuotRow0ConcreteExtractAtOrder_frontier :
  ∀ (m : ℕ) (s : OffSeed Xi), XiJetQuotRow0ConcreteExtractAtOrder m s

end XiPacket
end Targets
end Hyperlocal
