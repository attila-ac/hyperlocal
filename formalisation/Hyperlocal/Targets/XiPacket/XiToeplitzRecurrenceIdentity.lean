/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentity.lean

  Facade import surface for Toeplitz recurrence identity consumers.

  Policy:
  * This file is theorem-only and defines NOTHING.
  * It exists only to provide a stable place for downstream to import, while the
    actual proofs live in the split files:
      - XiToeplitzRecurrenceIdentityRe.lean
      - XiToeplitzRecurrenceIdentityIm.lean

  What you get after importing THIS file:

    From the real-pivot half:
      xiToeplitzRecurrenceIdentity_atOrder
      xiToeplitzRecurrenceIdentity_p_of_kappaAt0

    From the imag-pivot half:
      xiToeplitzRecurrenceIdentity_atOrder_im
      xiToeplitzRecurrenceIdentity_p

  IMPORTANT:
  Do not reintroduce any legacy anchor injector dependencies here.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentityRe
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentityIm

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- Intentionally empty: all declarations are provided by the imported split files.

end XiPacket
end Targets
end Hyperlocal
