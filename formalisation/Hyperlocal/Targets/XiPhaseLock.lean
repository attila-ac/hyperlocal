/-
  Hyperlocal/Targets/XiPhaseLock.lean

  Targets-level stage-3 bridge surface.

  IMPORTANT:
  This file should install exactly one sigma-at-order provider instance and one
  coords01-at-order provider instance, both at the end-claim cone only.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderInstallerFromRow0FrontierAtOrder
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderInstallerFromSigmaAndRow012TrueAnalytic

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Transport.OffSeedBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

abbrev Xi := Hyperlocal.Targets.XiPacket.Xi

theorem xi_phaseLock : Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.offSeedPhaseLock_Xi

theorem Stage3Bridge :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge Xi := by
  exact Hyperlocal.Transport.stage3Bridge_of_phaseLock (H := Xi) xi_phaseLock

end Targets
end Hyperlocal
