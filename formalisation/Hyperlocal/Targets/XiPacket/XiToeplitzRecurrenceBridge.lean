/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceBridge.lean

  Compatibility shim.

  Option A places the unique Toeplitz/recurrence frontier in:
    `XiToeplitzRecurrenceExtract.lean` as
      `xiToeplitzEllOut_fromRecurrence : XiToeplitzEllOut s`.

  Some downstream files may still import this Bridge path.
  This file therefore contains *no* redeclarations; it only re-exports the
  Extract module.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- Intentionally empty: do NOT redeclare `xiToeplitzEllOut_fromRecurrence` here.

end XiPacket
end Targets
end Hyperlocal
