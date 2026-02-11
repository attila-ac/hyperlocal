/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcrete.lean

  Semantic bridge (collision-free name):

    xiRecRowPkg (packaged, to be replaced by the jet-quotient recurrence operator)
      ⇒ XiMinimalModelRecurrenceHyp   (manufacturing layer)
      ⇒ XiToeplitzEllOut              (extraction layer).

  IMPORTANT:
  We intentionally DO NOT redeclare the global name `xiToeplitzEllOut_fromRecurrence`
  (it may still exist in stale .olean artifacts). We use a fresh name `...C`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceMinimalModelProof

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Project-facing endpoint (collision-free): concrete recurrence rows ⇒ ℓ-vanishing output. -/
theorem xiToeplitzEllOut_fromRecurrenceC (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOut s := by
  exact xiToeplitzEllOut_of_minRecurrence (s := s)
    (xiMinimalModelRecurrenceHyp_fromConcrete (s := s))

end XiPacket
end Targets
end Hyperlocal
