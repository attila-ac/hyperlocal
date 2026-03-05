/-
  Hyperlocal/Targets/OffSeedPhaseLockXi.lean

  Targets-level export for `OffSeedPhaseLock Xi`.

  IMPORTANT:
  We intentionally re-export the *AXIOM-FREE mainline* Stage-3 consumer
  from `Targets/XiPacket/OffSeedPhaseLockXiPayloadAtOrder.lean`.

  This prevents the end-claim cone (e.g. `Targets/XiPhaseLock.lean`, `OneButton.lean`)
  from picking up legacy analytic staging (e.g. sigma-out staging providers).
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

/-- Stage-3 consumer (AXIOM-FREE mainline): `OffSeedPhaseLock Xi`. -/
theorem offSeedPhaseLock_Xi :
    Hyperlocal.Transport.OffSeedPhaseLock Hyperlocal.Targets.XiPacket.Xi :=
  Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi

end Targets
end Hyperlocal
