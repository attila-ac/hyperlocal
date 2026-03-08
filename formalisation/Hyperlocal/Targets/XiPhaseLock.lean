/-
  Hyperlocal/Targets/XiPhaseLock.lean
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderInstallerFromRow0FrontierAtOrder
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Transport.OffSeedBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

abbrev Xi := Hyperlocal.Targets.XiPacket.Xi

variable [_root_.Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]

/-- Mainline: `OffSeedPhaseLock Xi`. -/
theorem xi_phaseLock : Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.offSeedPhaseLock_Xi

/-- Stage-3 bridge: build `Conclusion.OffSeedToTAC.Stage3Bridge Xi`. -/
theorem Stage3Bridge :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge Xi := by
  exact Hyperlocal.Transport.stage3Bridge_of_phaseLock (H := Xi) xi_phaseLock

end Targets
end Hyperlocal
