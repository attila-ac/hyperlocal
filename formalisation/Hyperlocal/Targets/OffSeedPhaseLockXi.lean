/-
  Hyperlocal/Targets/OffSeedPhaseLockXi.lean
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-- Stage-3 consumer (AXIOM-FREE mainline): `OffSeedPhaseLock Xi`. -/
theorem offSeedPhaseLock_Xi
    [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
    [_root_.Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]
    [_root_.Hyperlocal.Targets.XiPacket.RouteAWcScalarProvider] :
    Hyperlocal.Transport.OffSeedPhaseLock Hyperlocal.Targets.XiPacket.Xi :=
  Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi

end Targets
end Hyperlocal
