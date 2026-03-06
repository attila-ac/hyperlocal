/-
  Hyperlocal/Targets/XiPhaseLock.lean

  Targets-level stage-3 bridge surface.

  IMPORTANT:
  This file should install exactly one sigma-at-order provider instance.
  Therefore it imports the Row0-frontier installer (theorem route),
  and MUST NOT import the legacy axiom-provider file.

  ALSO (cycle policy):
  End-claim cone is allowed to import theorem-side / installer modules that realize
  interfaces. Upstream firewall modules must NOT.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderInstallerFromRow0FrontierAtOrder

-- End-claim-only: use the theorem-side coords01 provider surface.
-- Do NOT import the upstream fallback installer here.
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Transport.OffSeedBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

/-- The concrete ξ used in Targets-land. -/
abbrev Xi := Hyperlocal.Targets.XiPacket.Xi

/-- Mainline: `OffSeedPhaseLock Xi`. -/
theorem xi_phaseLock : Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.offSeedPhaseLock_Xi

/-- Stage-3 bridge: build `Conclusion.OffSeedToTAC.Stage3Bridge Xi`. -/
theorem Stage3Bridge :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge Xi := by
  exact Hyperlocal.Transport.stage3Bridge_of_phaseLock (H := Xi) xi_phaseLock

end Targets
end Hyperlocal
