/-
  Hyperlocal/Targets/OffSeedPhaseLockXi.lean
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

/-- Stage-3 consumer (AXIOM-FREE mainline): `OffSeedPhaseLock Xi`. -/
theorem offSeedPhaseLock_Xi
    [_root_.Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider] :
    Hyperlocal.Transport.OffSeedPhaseLock Hyperlocal.Targets.XiPacket.Xi :=
  Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi

end Targets
end Hyperlocal
