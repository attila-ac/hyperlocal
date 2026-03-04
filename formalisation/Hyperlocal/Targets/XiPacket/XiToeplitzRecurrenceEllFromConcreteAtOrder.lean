/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrder.lean

  Semantic bridge (AtOrder): concrete Toeplitz/recurrence output ⇒ ℓ-vanishing
  for the jet-pivot windows at order `m`.

  Status (2026-03-04): theorem-level.

  Pattern (mirrors sigma/coords01 elimination):
  * keep this file import-light (stable downstream surface)
  * move the concrete operator proof to an upstream module

  This avoids import cycles with `XiToeplitzRecurrenceIdentity(Re/Im)`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderProofUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Route--B “AtOrder” ℓ-output (theorem-level; proof is upstream). -/
theorem xiToeplitzEllOutAt_fromRecurrenceC
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOutAt m s :=
  xiToeplitzEllOutAt_fromRecurrenceC_proof (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
