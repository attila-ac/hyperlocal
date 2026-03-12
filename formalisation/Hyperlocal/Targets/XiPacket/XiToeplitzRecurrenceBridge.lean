/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceBridge.lean

  Bridge glue (kept lightweight).

  NOTE:
  `xiToeplitzEllOut_fromRecurrence` is now the semantic frontier axiom
  provided by `XiToeplitzRecurrenceExtract.lean`. We do NOT redefine it here.

  2026-03-13 honest post-axiom state:
  * the semantics-layer kernel endpoint is now theorem-gated
  * therefore this bridge wrapper can no longer remain assumption-free
  * it must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceSemantics
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-- Public endpoint: SpanOut from the kernel (semantics layer). -/
theorem xiToeplitzSpanOut_fromRecurrence
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiToeplitzSpanOut s := by
  exact (xiToeplitzKernelOut_fromRecurrence (s := s)).toSpanOut

end XiPacket
end Targets
end Hyperlocal
