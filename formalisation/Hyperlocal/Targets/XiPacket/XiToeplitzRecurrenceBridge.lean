/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceBridge.lean

  Plan C++: isolate the FINAL ξ-specific Toeplitz/recurrence semantic cliff
  into a *dedicated* bridge file.

  “Best of both worlds”:
  * the axiom is stated in the weaker / structural form (SpanOut),
  * downstream keeps consuming the stronger / convenient form (EllOut),
    obtained as a theorem from SpanOut via multilinearity.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport

/-
  FINAL SEMANTIC CLIFF (and only one in this layer):

  Later: prove this from the concrete ξ Toeplitz/recurrence extraction lemma.
-/
axiom xiToeplitzSpanOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzSpanOut s

/-- Downstream-facing theorem: the ℓ-vanishings needed by Lemma-C plumbing. -/
theorem xiToeplitzEllOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOut s :=
  XiToeplitzEllOut.of_spanOut (s := s)
    (xiToeplitzSpanOut_fromRecurrence (s := s))

end XiPacket
end Targets
end Hyperlocal
