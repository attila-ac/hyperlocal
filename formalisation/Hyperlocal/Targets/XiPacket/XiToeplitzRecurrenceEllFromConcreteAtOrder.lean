/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrder.lean

  Semantic bridge (AtOrder): concrete Toeplitz/recurrence output ⇒ ℓ-vanishing
  for the jet-pivot windows at order `m`.

  This is the next “real milestone” for Option-ELL:
  it allows deriving `bCoeff = 0` using κ-nonvanishing witnessed at some
  jet order (from jet-nonflatness), without assuming the legacy value-level
  anchor nonvanishing axiom.

  Current status:
  * This is still a semantic cliff: the actual recurrence-extraction theorem
    for order-`m` jets is not yet formalised.
  * The interface is isolated here so it can later be discharged by a theorem
    without touching downstream algebra.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Semantic endpoint (temporary): Toeplitz/recurrence extraction provides the two
ℓ-vanishings for the order-`m` jet-pivot windows.
-/
axiom xiToeplitzEllOutAt_fromRecurrenceC (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOutAt m s

end XiPacket
end Targets
end Hyperlocal
