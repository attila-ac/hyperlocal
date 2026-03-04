/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrder.lean

  Semantic bridge (AtOrder): concrete Toeplitz/recurrence output ⇒ ℓ-vanishing
  for the jet-pivot windows at order `m`.

  NOTE:
  This is currently a *semantic cliff* (axiom-stub) to keep the DAG green while
  the Row0-frontier-at-order spec layer and the Option-ELL pipeline are being
  reorganized. We preserve the historical theorem name for downstream stability.

  Later: discharge this axiom by the proof you started (Row0 frontier ⇒ ToeplitzRow3 ⇒ ell=0).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Route--B “AtOrder” ℓ-output (currently staged as a semantic cliff). -/
axiom xiToeplitzEllOutAt_fromRecurrenceC
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOutAt m s

end XiPacket
end Targets
end Hyperlocal
