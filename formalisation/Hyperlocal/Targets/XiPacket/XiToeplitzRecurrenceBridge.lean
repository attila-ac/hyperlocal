/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceBridge.lean

  Bridge glue (kept lightweight).

  NOTE:
  `xiToeplitzEllOut_fromRecurrence` is now the semantic frontier axiom
  provided by `XiToeplitzRecurrenceExtract.lean`. We do NOT redefine it here.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceSemantics

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Public endpoint: SpanOut from the kernel (semantics layer). -/
theorem xiToeplitzSpanOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzSpanOut s := by
  exact (xiToeplitzKernelOut_fromRecurrence (s := s)).toSpanOut

end XiPacket
end Targets
end Hyperlocal
