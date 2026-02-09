/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceBridge.lean

  Public endpoints live here (and only here).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceSemantics
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport

/-- Public endpoint: SpanOut from the kernel. -/
theorem xiToeplitzSpanOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzSpanOut s :=
  (xiToeplitzKernelOut_fromRecurrence (s := s)).toSpanOut

/-- Public endpoint: EllOut from the kernel (via SpanOut ⇒ EllOut). -/
theorem xiToeplitzEllOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOut s :=
  XiToeplitzEllOut_of_kernel (s := s) (xiToeplitzKernelOut_fromRecurrence (s := s))

end XiPacket
end Targets
end Hyperlocal
