/-
  Installs the sigma-at-order provider.

  Policy:
  * This file is a stable import surface.
  * It MUST NOT define a competing instance.
  * The actual instance is provided by `XiRow0Bridge_AtOrderSigmaProviderTheorem`,
    which is now theorem-backed (not axiom-backed).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- no declarations; just re-export the installed instance

end XiPacket
end Targets
end Hyperlocal
